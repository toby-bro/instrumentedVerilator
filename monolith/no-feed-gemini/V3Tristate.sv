module tri_basic (
    input logic i_enable,
    input logic i_data,
    output logic o_out
);
    assign o_out = i_enable ? i_data : 1'bz;
endmodule
module tri_pull (
    input logic i_data_in,
    inout wire o_bi_dir
);
    pullup (o_bi_dir); 
    assign o_bi_dir = i_data_in; 
endmodule
module tri_bufif (
    input logic i_in,
    input logic i_control,
    output logic o_out_bufif
);
    bufif1 (o_out_bufif, i_in, i_control);
endmodule
module tri_wired_nets (
    input logic i_data1,
    input logic i_data2,
    input logic i_data3,
    output logic o_final_wor
);
    wor wire w_temp;
    assign w_temp = i_data1;
    assign w_temp = i_data2;
    assign w_temp = i_data3;
    assign o_final_wor = w_temp;
endmodule
module tri_strength (
    input logic i_data_in,
    output logic o_strong_weak_out
);
    wire w_net;
    assign (strong1, weak0) w_net = i_data_in;
    assign (supply1, supply0) w_net = 1'b0;
    assign o_strong_weak_out = w_net;
endmodule
module tri_select_concat (
    input wire [7:0] i_bus_in,
    input logic i_en_bit,
    input logic i_en_slice,
    input logic i_en_concat_lsb,
    input logic i_en_concat_msb,
    output logic o_bit_out,
    output logic [3:0] o_slice_out,
    output logic [1:0] o_concat_out
);
    wire w_bit_tri;
    wire [3:0] w_slice_tri;
    wire [0:0] w_concat_tri_lsb;
    wire [0:0] w_concat_tri_msb;
    assign w_bit_tri = i_en_bit ? i_bus_in[0] : 1'bz;
    assign o_bit_out = w_bit_tri;
    assign w_slice_tri = i_en_slice ? i_bus_in[7:4] : 4'bz;
    assign o_slice_out = w_slice_tri;
    assign w_concat_tri_lsb = i_en_concat_lsb ? i_bus_in[1] : 1'bz;
    assign w_concat_tri_msb = i_en_concat_msb ? i_bus_in[0] : 1'bz;
    assign o_concat_out = {w_concat_tri_lsb, w_concat_tri_msb};
endmodule
module tri_lhs_select (
    input logic i_data_in,
    input logic i_enable_bit,
    input logic [7:0] i_full_bus_data,
    input logic i_enable_slice,
    output logic [7:0] o_tristate_bus
);
    wire [7:0] w_internal_tristate_bus;
    wire [0:0] w_msb_part;
    wire [0:0] w_lsb_part;
    assign w_internal_tristate_bus = 8'b0; 
    assign w_internal_tristate_bus[0] = i_enable_bit ? i_data_in : 1'bz;
    assign w_internal_tristate_bus[3:2] = i_enable_slice ? i_full_bus_data[1:0] : 2'bz;
    assign {w_msb_part, w_lsb_part} = i_enable_bit ? 2'b10 : 2'bz;
    assign o_tristate_bus = w_internal_tristate_bus;
endmodule
module tri_case_eq (
    input wire [1:0] i_val,
    input wire i_control_z,
    output logic o_eq_case_out,
    output logic o_neq_case_out
);
    wire [1:0] w_val_with_z;
    assign w_val_with_z = i_control_z ? 2'b1z : i_val;
    assign o_eq_case_out = (w_val_with_z === 2'b1z);
    assign o_neq_case_out = (w_val_with_z !== 2'b10);
endmodule
module tri_case_stmt (
    input wire [1:0] i_sel_val,
    output logic o_case_out
);
    reg r_out;
    always_comb begin
        r_out = 1'b0;
        casez (i_sel_val)
            2'b0z: r_out = 1'b1;
            2'b10: r_out = 1'b0;
            default: r_out = 1'bx;
        endcase
    end
    assign o_case_out = r_out;
endmodule
module tri_count_bits (
    input wire [3:0] i_data_in,
    output integer o_count_ones_out,
    output integer o_count_zeros_out
);
    wire [3:0] w_data_with_z;
    assign w_data_with_z = (i_data_in[0]) ? 4'b101z : i_data_in;
    assign o_count_ones_out = $countones(w_data_with_z);
    assign o_count_zeros_out = $countzeros(w_data_with_z);
endmodule
module tri_hierarchy_sub_unconnected (
    input logic sub_in,
    inout wire sub_io,
    output logic sub_out,
    output logic sub_unconnected_out
);
    assign sub_io = sub_in ? 1'b1 : 1'bz;
    assign sub_out = sub_io;
endmodule
module tri_inout_pin (
    input logic top_in,
    inout wire top_io,
    output logic top_out,
    output logic top_unconnected_sub_out
);
    wire internal_sub_in;
    wire internal_sub_io;
    wire internal_sub_out;
    wire internal_sub_unconnected_out;
    assign internal_sub_in = top_in;
    assign top_out = internal_sub_out;
    assign top_unconnected_sub_out = internal_sub_unconnected_out;
    tri_hierarchy_sub_unconnected u_sub_tri (
        .sub_in (internal_sub_in),
        .sub_io (internal_sub_io),
        .sub_out(internal_sub_out),
        .sub_unconnected_out() 
    );
    assign top_io = internal_sub_io;
    assign top_io = (top_in) ? 1'b0 : 1'bz;
endmodule
module tri_cond_and_or (
    input logic i_sel,
    input logic i_val1,
    input logic i_val2,
    input logic i_en1,
    input logic i_en2,
    output logic o_cond_out,
    output logic o_and_out,
    output logic o_or_out
);
    wire w_val1_tri;
    wire w_val2_tri;
    assign w_val1_tri = i_en1 ? i_val1 : 1'bz;
    assign w_val2_tri = i_en2 ? i_val2 : 1'bz;
    assign o_cond_out = i_sel ? w_val1_tri : w_val2_tri;
    assign o_and_out = w_val1_tri & w_val2_tri;
    assign o_or_out = w_val1_tri | w_val2_tri;
endmodule
