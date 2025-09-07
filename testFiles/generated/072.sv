interface my_if;
    logic [7:0] data;
    logic ready;
    logic valid;
    modport FullAccess (input data, output ready, output valid);
    modport AccessIn (output data, output valid, input ready);
    modport AccessOut (input data, input valid, output ready);
endinterface
module GenerateIfParam #(
    parameter bit GEN = 1
) (
    input logic sig_in,
    output logic sig_out
);
    generate
        if (GEN) begin : g_true
            assign sig_out = sig_in;
        end
        else begin : g_false
            assign sig_out = ~sig_in;
        end
    endgenerate
endmodule

module StructExample (
    input logic [15:0] in_data,
    output logic [7:0] out_field_a,
    output logic [7:0] out_field_b
);
    typedef struct packed {
        logic [7:0] field_a;
        logic [7:0] field_b;
    } example_struct_t;
    example_struct_t my_struct;
    always_comb begin
        my_struct     = in_data;
        out_field_a   = my_struct.field_a;
        out_field_b   = my_struct.field_b;
    end
endmodule

module module_to_bind (
    input logic i_bind_clk,
    input logic [3:0] i_bind_control,
    output logic o_bind_status
);
    always_comb o_bind_status = |i_bind_control;
endmodule

module module_assign_nonblocking (
    input logic clk,
    input logic [7:0] in_value,
    input logic reset,
    output logic out_data_q
);
    my_if vif_inst();
    logic [7:0] data_q;
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            vif_inst.data <= 8'h0;
            data_q <= 8'h0;
        end else begin
            vif_inst.data <= in_value;
            data_q <= vif_inst.data;
        end
    end
    assign out_data_q = data_q;
endmodule

module target_module_for_bind (
    input logic i_target_clk,
    input logic [7:0] i_target_data,
    output logic [7:0] o_target_result
);
    always_comb o_target_result = i_target_data + 1;
endmodule

module bind_directive_top (
    input logic i_clk,
    input logic [3:0] i_control,
    input logic [7:0] i_data,
    output logic [7:0] o_result,
    output logic o_status
);
    target_module_for_bind target_inst(
        .i_target_clk   (i_clk),
        .i_target_data  (i_data),
        .o_target_result(o_result)
    );
    module_to_bind bind_inst(
        .i_bind_clk     (i_clk),
        .i_bind_control (i_control),
        .o_bind_status  (o_status)
    );
endmodule

module snippet (
    input wire clk,
    input logic [7:0] inj_b_bb_1755007776006_657,
    input logic [7:0] inj_c_bb_1755007776006_641,
    input logic inj_enable_pa_1755007776002_577,
    input logic [15:0] inj_in_data_1755007776003_583,
    input int inj_in_val_1755007776004_557,
    input logic [7:0] inj_in_value_1755007776003_748,
    input logic [31:0] inj_input_pa_1755007776002_550,
    input logic [3:0] inj_input_slice_pa_1755007776002_294,
    input wire reset,
    output logic inj_concat_port_output_1755007776008_76,
    output int inj_config_data_out_1755007776005_793,
    output logic [1:0] inj_non_ansi_i_1755007776008_425,
    output logic [1:0] inj_non_ansi_j_1755007776008_534,
    output logic [7:0] inj_o_result_1755007776007_342,
    output logic inj_o_status_1755007776007_42,
    output logic inj_out_data_q_1755007776003_240,
    output logic [7:0] inj_out_field_a_1755007776003_93,
    output logic [7:0] inj_out_field_b_1755007776003_271,
    output int inj_out_val_1755007776004_430,
    output logic [7:0] inj_output_pa_1755007776002_179,
    output logic [7:0] inj_output_pa_element1_1755007776002_69,
    output logic inj_sig_out_1755007776004_865,
    output logic [7:0] inj_x_bb_1755007776006_741,
    output logic [7:0] inj_y_bb_1755007776006_142,
    output logic [7:0] inj_z_bb_1755007776006_180
);
    // BEGIN: module_packed_array_ts1755007776002
    logic [7:0] my_packed_array[0:3] ;
    // BEGIN: nested_macro_expansion_ts1755007776004
    `define LVL1(x) ((x) + 1)
    `define LVL2(y) `LVL1((y) * 2)
    `define LVL3(z) `LVL2((z) / 3)
    int nested_result_ts1755007776004;
        // BEGIN: split_combo_nb_ts1755007776006
        logic [7:0] temp_bb_ts1755007776006;
            // BEGIN: non_ansi_concat_port_ts1755007776009
            output logic [1:0] inj_non_ansi_i_1755007776008_425_ts1755007776008;
            output logic [1:0] inj_non_ansi_j_1755007776008_534_ts1755007776008;
            input logic inj_enable_pa_1755007776002_577_ts1755007776008;
            output logic inj_concat_port_output_1755007776008_76_ts1755007776008;
            assign inj_non_ansi_i_1755007776008_425_ts1755007776008 = 2'b10;
            assign inj_non_ansi_j_1755007776008_534_ts1755007776008 = 2'b01;
            assign inj_concat_port_output_1755007776008_76_ts1755007776008 = inj_enable_pa_1755007776002_577_ts1755007776008;
            // END: non_ansi_concat_port_ts1755007776009

            bind_directive_top bind_directive_top_inst_1755007776007_7301 (
                .i_control(inj_input_slice_pa_1755007776002_294),
                .i_data(inj_b_bb_1755007776006_657),
                .o_result(inj_o_result_1755007776007_342),
                .o_status(inj_o_status_1755007776007_42),
                .i_clk(clk)
            );
        always @(posedge clk) begin
            inj_x_bb_1755007776006_741 <= inj_in_value_1755007776003_748 + inj_b_bb_1755007776006_657;
            inj_y_bb_1755007776006_142 <= inj_x_bb_1755007776006_741 - inj_c_bb_1755007776006_641;
            inj_z_bb_1755007776006_180 <= inj_in_value_1755007776003_748 * inj_c_bb_1755007776006_641;
        end
        // END: split_combo_nb_ts1755007776006

        // BEGIN: PragmaProtectOptions_ts1755007776005
    `ifdef SLANG_PRAGMA
    `protect encoding (enctype="base64", line_length=76, bytes=1024)
    `endif
    `ifdef SLANG_PRAGMA
    `protect license (library="my_project_lib", entry="start_feature_A", match=42, feature="feature_set_B", exit="end_feature_A")
    `endif
    `ifdef SLANG_PRAGMA
    `protect reset
    `endif
    `ifdef SLANG_PRAGMA
    `protect viewport (object="design.module_a.instance_b.register_c", access="read-only")
    `endif
    assign inj_config_data_out_1755007776005_793 = inj_in_val_1755007776004_557 + 1;
        // END: PragmaProtectOptions_ts1755007776005

    always_comb begin
        nested_result_ts1755007776004 = `LVL3(`LVL1(inj_in_val_1755007776004_557));
    end
    assign inj_out_val_1755007776004_430 = nested_result_ts1755007776004;
    // END: nested_macro_expansion_ts1755007776004

    GenerateIfParam GenerateIfParam_inst_1755007776004_64 (
        .sig_in(inj_enable_pa_1755007776002_577),
        .sig_out(inj_sig_out_1755007776004_865)
    );
    module_assign_nonblocking module_assign_nonblocking_inst_1755007776003_7512 (
        .out_data_q(inj_out_data_q_1755007776003_240),
        .clk(clk),
        .in_value(inj_in_value_1755007776003_748),
        .reset(reset)
    );
    StructExample StructExample_inst_1755007776003_7696 (
        .out_field_b(inj_out_field_b_1755007776003_271),
        .in_data(inj_in_data_1755007776003_583),
        .out_field_a(inj_out_field_a_1755007776003_93)
    );
    always_comb begin
        if (inj_enable_pa_1755007776002_577) begin
            my_packed_array[0] = inj_input_pa_1755007776002_550[7:0];
            my_packed_array[1] = inj_input_pa_1755007776002_550[15:8];
            my_packed_array[2] = inj_input_pa_1755007776002_550[23:16];
            my_packed_array[3] = my_packed_array[0] + my_packed_array[1];
        end else begin
            my_packed_array[0] = 8'h0;
            my_packed_array[1] = 8'h0;
            my_packed_array[2] = 8'h0;
            my_packed_array[3] = 8'h0;
        end
        my_packed_array[0][3:0] = inj_input_slice_pa_1755007776002_294;
    end
    assign inj_output_pa_1755007776002_179 = my_packed_array[3];
    assign inj_output_pa_element1_1755007776002_69 = my_packed_array[1];
    // END: module_packed_array_ts1755007776002
endmodule

