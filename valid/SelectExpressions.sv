module element_select_packed_array(
    input  logic [31:0] in_data,
    input  logic [1:0]  index,
    output logic [7:0]  out_byte
);
    logic [3:0][7:0] packed_arr;
    always_comb begin
        packed_arr = in_data;
        out_byte   = packed_arr[index];
    end
endmodule
module element_select_unpacked_array(
    input  logic [7:0] in0,
    input  logic [7:0] in1,
    input  logic [7:0] in2,
    input  logic [7:0] in3,
    input  logic [1:0] index,
    output logic [7:0] out_byte
);
    logic [7:0] unpacked_arr [0:3];
    always_comb begin
        unpacked_arr[0] = in0;
        unpacked_arr[1] = in1;
        unpacked_arr[2] = in2;
        unpacked_arr[3] = in3;
        out_byte        = unpacked_arr[index];
    end
endmodule
module range_select_indexed_up(
    input  logic [31:0] in_vec,
    input  logic [4:0]  base,
    output logic [7:0]  out_slice
);
    always_comb begin
        out_slice = in_vec[base +: 8];
    end
endmodule
module range_select_indexed_down(
    input  logic [31:0] in_vec,
    input  logic [4:0]  base,
    output logic [7:0]  out_slice
);
    always_comb begin
        out_slice = in_vec[base -: 8];
    end
endmodule
module queue_element_select(
    input  logic [1:0] sel,
    output logic [31:0] q_elem
);
`ifdef VERILATOR_DEFINED_BUT_UNUSED
    assign q_elem = {30'd0, sel};
`else
    int q[$];
    always_comb begin
        q = '{10,20,30,40};
        q_elem = q[sel];
    end
`endif
endmodule
module assoc_array_element_select(
    input  logic [31:0] key,
    input  logic [31:0] val_in,
    output logic [31:0] val_out
);
`ifdef VERILATOR_DEFINED_BUT_UNUSED
    assign val_out = val_in ^ key;
`else
    int assoc[int];
    always_comb begin
        assoc[key] = val_in;
        val_out    = assoc[key];
    end
`endif
endmodule
module struct_member_access(
    input  logic [3:0] in_a,
    input  logic [3:0] in_b,
    output logic [3:0] out_b
);
    typedef struct packed {
        logic [3:0] a;
        logic [3:0] b;
    } packed_s;
    packed_s s;
    always_comb begin
        s.a   = in_a;
        s.b   = in_b;
        out_b = s.b;
    end
endmodule
module packed_union_access(
    input  logic [7:0] in_a,
    input  logic [7:0] in_b,
    output logic [7:0] out_sel
);
    typedef union packed {
        logic [7:0] a;
        logic [7:0] b;
    } u_packed_t;
    u_packed_t u;
    always_comb begin
        u.a     = in_a;
        out_sel = u.b ^ in_b;
    end
endmodule
module unpacked_union_access(
    input  logic [7:0] in_a,
    input  logic [7:0] in_b,
    input  logic       select,
    output logic [7:0] out_sel
);
    typedef union {
        logic [7:0] a;
        logic [7:0] b;
    } u_unpacked_t;
    u_unpacked_t u;
    always_comb begin
        if (select)
            u.a = in_a;
        else
            u.b = in_b;
        out_sel = select ? u.a : u.b;
    end
endmodule
module class_rand_mode_demo(
    input  logic dummy,
    output logic mode_bit
);
`ifdef VERILATOR_DEFINED_BUT_UNUSED
    assign mode_bit = dummy;
`else
    class my_c;
        rand bit [7:0] data;
    endclass
    my_c obj;
    always_comb begin
        obj = new();
        mode_bit = obj.data.rand_mode();
    end
`endif
endmodule
module vectored_net_select(
    input  logic [7:0] data_in,
    input  logic [2:0] idx,
    output logic sel_bit
);
`ifdef VERILATOR_DEFINED_BUT_UNUSED
    wire [7:0] temp = data_in;
    assign sel_bit = temp[idx];
`else
    wire vectored [7:0] vect_net;
    assign vect_net = data_in;
    assign sel_bit  = data_in[idx];
`endif
endmodule
module dynamic_array_element_select(
    input  logic [3:0] len,
    output logic [31:0] out_data
);
`ifdef VERILATOR_DEFINED_BUT_UNUSED
    assign out_data = {28'd0, len};
`else
    int dyn[];
    always_comb begin
        dyn = new[len];
        for (int i = 0; i < len; i++)
            dyn[i] = i;
        out_data = dyn[len ? (len - 1) : 0];
    end
`endif
endmodule
