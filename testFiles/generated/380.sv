interface cond_if;
    logic [15:0] control_reg;
    logic [15:0] status_reg;
    modport CtrlStat (output control_reg, input status_reg);
endinterface
interface struct_if;
    logic [7:0] packet_field1;
    logic [7:0] packet_field2;
    logic tx_en;
    modport Access (output packet_field1, output packet_field2, output tx_en);
endinterface
module ModuleBasic (
    input logic a,
    input int b,
    output logic out_a,
    output int out_b
);
    parameter int P1  = 10;
    localparam int LP1 = 20;
    logic c;
    int   d;
    always_comb begin
        logic temp_v;
        temp_v = d;
        c      = temp_v;
    end
    assign out_a = a;
    assign d     = b;
    assign out_b = d + P1 + LP1;
endmodule

module ModuleHierarchy_Low #(
    parameter int SEL_PARAM = 5
) (
    input logic [3:0] data_in,
    input int sel_in,
    output logic [7:0] data_out
);
    ModuleBasic m1 (
        .a     (1'b1),
        .b     (sel_in),
        .out_a (),
        .out_b ( )
    );
    if (SEL_PARAM > 5) begin : gen_high
        int high_data;
        ModuleBasic m_high (
            .a     (1'b0),
            .b     (SEL_PARAM),
            .out_a (),
            .out_b (high_data)
        );
    end else begin : gen_low
        int low_data;
        ModuleBasic m_low (
            .a     (1'b0),
            .b     (SEL_PARAM),
            .out_a (),
            .out_b (low_data)
        );
    end
    for (genvar i = 0; i < 2; ++i) begin : gen_loop
        logic [1:0] sub_in;
        assign sub_in = data_in[i*2 +: 2];
        int temp_int;
        ModuleBasic m_inst (
            .a      (1'b0),
            .b      (int'(sub_in)),
            .out_a  (),
            .out_b  (temp_int)
        );
        assign data_out[i*4 +: 4] = temp_int[3:0];
    end
endmodule

module ansi_directions (
    input logic control_in,
    input logic data_ref_in,
    output logic data_ref_out,
    output logic status_out,
    inout wire data_inout
);
    logic internal_data = 1'b0;
    assign data_inout = internal_data;
    always_comb begin
        data_ref_out = data_ref_in;
        internal_data = data_inout;
        status_out = internal_data | control_in;
    end
endmodule

module case_unique_casez_reordered_mod (
    input logic [1:0] case_expr,
    input logic [3:0] case_inside_val,
    output logic [4:0] internal_out
);
    always @* begin
        unique casez ({case_expr[0], case_inside_val[3:2], case_expr[1]})
            4'b1?0?: internal_out = 30;
            4'b?101: internal_out = 31;  
            4'b0?1?: internal_out = 32;
            4'b1?1?: internal_out = 33;  
            4'b?111: internal_out = 34;  
        endcase
    end
endmodule

module mod_event_implicit (
    input wire [3:0] data_in,
    output reg [3:0] data_out
);
    always @* begin
        data_out = data_in;
    end
endmodule

module mod_internal_if_test (
    input wire in_i,
    output logic out_o
);
    assign out_o = !in_i;
endmodule

module split_conditional_blocking (
    input logic condition_o,
    input logic [7:0] in_false_o,
    input logic [7:0] in_true_o,
    output logic [7:0] out_val_o
);
    always @(*) begin
        if (condition_o) begin
            out_val_o = in_true_o;
        end else begin
            out_val_o = in_false_o;
        end
    end
endmodule

module snippet (
    input wire clk,
    input logic [1:0] inj_case_expr_1755007881765_761,
    input logic [3:0] inj_data_in_1755007881751_30,
    input wire [3:0] inj_data_in_1755007881756_538,
    input logic [15:0] inj_data_in_1755007881757_490,
    input logic inj_in1_1755007881750_303,
    input logic inj_in2_1755007881750_61,
    input wire [7:0] inj_in_array_data_1755007881760_178,
    input logic [7:0] inj_in_false_o_1755007881753_106,
    input logic [7:0] inj_in_true_o_1755007881753_510,
    input int inj_sel_in_1755007881751_27,
    input wire [1:0] inj_select_idx_1755007881760_282,
    input logic [3:0] inj_v2_1755007881753_809,
    input wire reset,
    output logic inj_control_status_1755007881757_135,
    output logic [7:0] inj_data_out_1755007881751_434,
    output reg [3:0] inj_data_out_1755007881756_42,
    output logic inj_data_ref_out_1755007881762_27,
    output logic inj_eq_1755007881753_793,
    output logic [4:0] inj_internal_out_1755007881765_808,
    output logic inj_o_done_ni_1755007881752_321,
    output logic inj_out1_1755007881750_388,
    output logic inj_out2_1755007881750_20,
    output logic inj_out_a_1755007881764_942,
    output int inj_out_b_1755007881764_696,
    output wire [3:0] inj_out_element_1755007881760_259,
    output logic inj_out_o_1755007881757_102,
    output logic [7:0] inj_out_val_o_1755007881753_917,
    output int inj_output_int_1755007881755_499,
    output logic inj_q_1755007881753_845,
    output logic inj_q_1755007881754_766,
    output logic inj_reset_n_1755007881759_864,
    output logic inj_status_out_1755007881762_315,
    output logic inj_tx_status_1755007881768_930,
    inout wire inj_data_inout_1755007881762_915
);
    // BEGIN: module_unpacked_array_ts1755007881750
    logic [1:0] data_ua[0:1] ;
    // BEGIN: mod_no_inline_module_ts1755007881752
    logic r_toggle = 1'b0;
    // BEGIN: func_macro_args_ts1755007881755
    `define ADD(a, b)       ((a) + (b))
    `define SUBTRACT(x, y)  ((x) - (y))
    localparam int P1_ADD = `ADD(10, 20);
    int p2_sub_var_ts1755007881755;
        // BEGIN: unpacked_array_module_ts1755007881760
        logic [3:0] data_array_ts1755007881760 [4];
            // BEGIN: module_struct_write_ts1755007881768
            struct_if stif_inst();
            always_comb begin
                stif_inst.packet_field1 = inj_in_false_o_1755007881753_106;
                stif_inst.packet_field2 = inj_in_true_o_1755007881753_510;
                stif_inst.tx_en = 1'b1;
                inj_tx_status_1755007881768_930 = stif_inst.tx_en;
            end
            // END: module_struct_write_ts1755007881768

            case_unique_casez_reordered_mod case_unique_casez_reordered_mod_inst_1755007881765_4304 (
                .case_expr(inj_case_expr_1755007881765_761),
                .case_inside_val(inj_v2_1755007881753_809),
                .internal_out(inj_internal_out_1755007881765_808)
            );
            ModuleBasic ModuleBasic_inst_1755007881764_7294 (
                .a(inj_in2_1755007881750_61),
                .b(inj_sel_in_1755007881751_27),
                .out_a(inj_out_a_1755007881764_942),
                .out_b(inj_out_b_1755007881764_696)
            );
            ansi_directions ansi_directions_inst_1755007881762_1670 (
                .control_in(inj_in1_1755007881750_303),
                .data_ref_in(inj_in2_1755007881750_61),
                .data_ref_out(inj_data_ref_out_1755007881762_27),
                .status_out(inj_status_out_1755007881762_315),
                .data_inout(inj_data_inout_1755007881762_915)
            );
        always @(*) begin
            data_array_ts1755007881760[0] = inj_in_array_data_1755007881760_178[3:0];
            data_array_ts1755007881760[1] = inj_in_array_data_1755007881760_178[7:4];
            data_array_ts1755007881760[2] = 4'd8;
            data_array_ts1755007881760[3] = 4'd12;
        end
        assign inj_out_element_1755007881760_259 = data_array_ts1755007881760[inj_select_idx_1755007881760_282];
        // END: unpacked_array_module_ts1755007881760

        // BEGIN: ansi_basic_ts1755007881759
        always_comb begin
            inj_reset_n_1755007881759_864 = clk;
        end
        // END: ansi_basic_ts1755007881759

        // BEGIN: module_conditional_write_ts1755007881758
        cond_if cif_inst();
        always_comb begin
            if (inj_in1_1755007881750_303) begin
                cif_inst.control_reg = inj_data_in_1755007881757_490;
            end else begin
                cif_inst.control_reg = 16'h0;
            end
            inj_control_status_1755007881757_135 = (cif_inst.control_reg != 16'h0);
        end
        // END: module_conditional_write_ts1755007881758

        mod_internal_if_test mod_internal_if_test_inst_1755007881757_6619 (
            .in_i(reset),
            .out_o(inj_out_o_1755007881757_102)
        );
        mod_event_implicit mod_event_implicit_inst_1755007881756_3563 (
            .data_in(inj_data_in_1755007881756_538),
            .data_out(inj_data_out_1755007881756_42)
        );
    always_comb begin
        p2_sub_var_ts1755007881755 = `SUBTRACT(50, inj_sel_in_1755007881751_27);
    end
    assign inj_output_int_1755007881755_499 = P1_ADD + p2_sub_var_ts1755007881755;
    // END: func_macro_args_ts1755007881755

    // BEGIN: basic_d_flipflop_ts1755007881754
    always_ff @(posedge clk) begin
        inj_q_1755007881754_766 <= inj_in1_1755007881750_303;
    end
    // END: basic_d_flipflop_ts1755007881754

    split_conditional_blocking split_conditional_blocking_inst_1755007881753_2484 (
        .in_false_o(inj_in_false_o_1755007881753_106),
        .in_true_o(inj_in_true_o_1755007881753_510),
        .out_val_o(inj_out_val_o_1755007881753_917),
        .condition_o(inj_in2_1755007881750_61)
    );
    // BEGIN: ModCompareVec_ts1755007881753
    assign inj_eq_1755007881753_793 = (inj_data_in_1755007881751_30 == inj_v2_1755007881753_809);
    // END: ModCompareVec_ts1755007881753

    // BEGIN: basic_d_flipflop_ts1755007881753
    always_ff @(posedge clk) begin
        inj_q_1755007881753_845 <= inj_in1_1755007881750_303;
    end
    // END: basic_d_flipflop_ts1755007881753

    always_ff @(posedge clk) begin
        r_toggle <= ~r_toggle;
    end
    assign inj_o_done_ni_1755007881752_321 = r_toggle;
    // END: mod_no_inline_module_ts1755007881752

    ModuleHierarchy_Low ModuleHierarchy_Low_inst_1755007881751_6884 (
        .sel_in(inj_sel_in_1755007881751_27),
        .data_out(inj_data_out_1755007881751_434),
        .data_in(inj_data_in_1755007881751_30)
    );
    always_comb begin
        data_ua[0][0] = inj_in1_1755007881750_303;
        data_ua[0][1] = inj_in2_1755007881750_61;
        data_ua[1][0] = data_ua[0][0];
        data_ua[1][1] = ~data_ua[0][1];
    end
    assign inj_out1_1755007881750_388 = data_ua[1][0];
    assign inj_out2_1755007881750_20 = data_ua[1][1];
    // END: module_unpacked_array_ts1755007881750
endmodule

