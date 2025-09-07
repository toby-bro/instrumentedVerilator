interface my_if;
    logic [7:0] data;
    logic ready;
    logic valid;
    modport FullAccess (input data, output ready, output valid);
    modport AccessIn (output data, output valid, input ready);
    modport AccessOut (input data, input valid, output ready);
endinterface
module ModuleGenerateIf (
    input logic [7:0] in_val,
    output logic [7:0] out_val
);
    parameter int PROCESS_ENABLE = 1;
    logic [7:0] processed_val;
    generate
        if (PROCESS_ENABLE) begin : process_block
            assign processed_val = in_val + 10;
        end else begin : bypass_block
            assign processed_val = in_val;
        end
    endgenerate
    assign out_val = processed_val;
endmodule

module PragmaProtectBoundaries (
    input logic start_protect,
    output logic protected_active
);
logic internal_state;
`ifdef SLANG_PRAGMA
`protect begin
`endif
assign internal_state = start_protect;
`ifdef SLANG_PRAGMA
`protect end
`endif
`ifdef SLANG_PRAGMA
`protect begin_protected
`endif
`ifdef SLANG_PRAGMA
`protect end_protected
`endif
assign protected_active = internal_state;
endmodule

module configuration_top (
    input logic i_in,
    output logic o_out
);
    assign o_out = i_in;
endmodule

module div_mod_ops (
    input logic [7:0] denominator,
    input logic [15:0] dividend_mod,
    input logic [7:0] divisor_mod,
    input logic [15:0] numerator,
    output logic [15:0] quotient,
    output logic [7:0] remainder
);
    assign quotient = (denominator == 0) ? 16'hFFFF : (numerator / denominator); 
    assign remainder = (divisor_mod == 0) ? 8'hFF : (dividend_mod % divisor_mod);
endmodule

module module_case_write (
    input logic [7:0] data_case_a,
    input logic [7:0] data_case_b,
    input logic [1:0] select_case,
    output logic case_output_ready
);
    my_if case_vif_inst();
    always_comb begin
        case (select_case)
            2'b00: begin
                case_vif_inst.data = 8'hAA;
                case_vif_inst.valid = 1'b1;
                case_vif_inst.ready = 1'b0;
            end
            2'b01: begin
                case_vif_inst.data = data_case_a;
                case_vif_inst.valid = 1'b0;
                case_vif_inst.ready = 1'b1;
            end
            2'b10: begin
                case_vif_inst.data = data_case_b;
                case_vif_inst.valid = 1'b1;
                case_vif_inst.ready = 1'b1;
            end
            default: begin
                case_vif_inst.data = 8'hFF;
                case_vif_inst.valid = 1'b0;
                case_vif_inst.ready = 1'b0;
            end
        endcase
        case_output_ready = case_vif_inst.ready;
    end
endmodule

module name_conflict_example (
    input logic i_in,
    output logic o_out
);
    parameter int my_param = 5;
    logic my_var;
    always_comb my_var = i_in;
    assign o_out = i_in && (my_param == 5) && my_var;
endmodule

module nested_macro_expansion (
    input int in_val,
    output int out_val
);
    `define LVL1(x) ((x) + 1)
    `define LVL2(y) `LVL1((y) * 2)
    `define LVL3(z) `LVL2((z) / 3)
    int nested_result;
    always_comb begin
        nested_result = `LVL3(`LVL1(in_val));
    end
    assign out_val = nested_result;
endmodule

module packed_struct_module (
    input wire [15:0] in_packed_data,
    output wire [7:0] out_byte
);
    typedef struct packed {
        logic [7:0] byte1;
        logic [7:0] byte2;
    } my_packed_struct_t;
    my_packed_struct_t data_struct;
    assign data_struct = in_packed_data;
    assign out_byte = data_struct.byte1;
endmodule

module snippet #(
    parameter integer UNUSED_PARAM = 8
) (
    input wire clk,
    input logic inj_b_1755007751754_292,
    input logic [3:0] inj_data_in_1755007751759_322,
    input logic [7:0] inj_denominator_1755007751753_99,
    input logic [15:0] inj_dividend_mod_1755007751753_480,
    input logic inj_i_in_1755007751752_75,
    input wire [2:0] inj_in_index_1755007751749_826,
    input wire [15:0] inj_in_packed_data_1755007751755_117,
    input wire [1:0] inj_in_part_lsb_1755007751749_411,
    input logic [7:0] inj_in_val_1755007751752_34,
    input int inj_in_val_1755007751755_982,
    input wire [7:0] inj_in_vector_1755007751749_932,
    input logic [2:0] inj_mode_1755007751762_521,
    input logic [15:0] inj_numerator_1755007751753_234,
    input logic [1:0] inj_select_case_1755007751757_694,
    input wire [31:0] inj_wide_in_1755007751749_790,
    input wire reset,
    output logic inj_case_output_ready_1755007751757_671,
    output logic [3:0] inj_data_out_1755007751759_334,
    output wire [7:0] inj_lower_byte_out_1755007751749_140,
    output logic inj_o_out_1755007751752_705,
    output logic inj_o_out_1755007751761_631,
    output logic [7:0] inj_o_target_result_1755007751769_610,
    output logic inj_out_bit_select_1755007751749_119,
    output logic [7:0] inj_out_bitwise_ops_1755007751749_266,
    output wire [7:0] inj_out_byte_1755007751755_853,
    output wire [7:0] inj_out_data_1755007751750_980,
    output logic inj_out_n_1755007751766_983,
    output logic [3:0] inj_out_part_select_1755007751749_766,
    output int inj_out_port_1755007751758_432,
    output logic [7:0] inj_out_val_1755007751752_33,
    output int inj_out_val_1755007751755_460,
    output logic [7:0] inj_out_vector_assign_1755007751749_231,
    output logic inj_protected_active_1755007751772_807,
    output logic [15:0] inj_quotient_1755007751753_548,
    output logic [7:0] inj_remainder_1755007751753_574,
    output logic [7:0] inj_res_1755007751762_461,
    output logic inj_sum_1755007751754_197,
    output wire [7:0] inj_upper_byte_out_1755007751749_681
);
    // BEGIN: part_select_ops_ts1755007751749
    wire [31:0] processed_wide_ts1755007751749;
        // BEGIN: simple_comb_ts1755007751751
        wire [7:0] intermediate_a_ts1755007751751;
        wire [7:0] intermediate_b_ts1755007751751;
        wire [7:0] intermediate_c_ts1755007751751;
            PragmaProtectBoundaries PragmaProtectBoundaries_inst_1755007751772_5146 (
                .start_protect(inj_b_1755007751754_292),
                .protected_active(inj_protected_active_1755007751772_807)
            );
            // BEGIN: target_module_for_bind_ts1755007751769
            always_comb inj_o_target_result_1755007751769_610 = inj_denominator_1755007751753_99 + 1;
            // END: target_module_for_bind_ts1755007751769

            // BEGIN: LintParamUnused_ts1755007751766
            assign inj_out_n_1755007751766_983 = inj_i_in_1755007751752_75;
            // END: LintParamUnused_ts1755007751766

            // BEGIN: dup_nested_if_ts1755007751763
            always_comb begin
                inj_res_1755007751762_461 = '0;
                if (inj_mode_1755007751762_521 == 3'b001) begin
                    if (inj_denominator_1755007751753_99 > inj_in_val_1755007751752_34) begin
                        inj_res_1755007751762_461 = inj_denominator_1755007751753_99 + inj_in_val_1755007751752_34;
                    end else begin
                        inj_res_1755007751762_461 = inj_denominator_1755007751753_99 - inj_in_val_1755007751752_34;
                    end
                end else if (inj_mode_1755007751762_521 == 3'b010) begin
                    if (inj_denominator_1755007751753_99 > inj_in_val_1755007751752_34) begin
                        inj_res_1755007751762_461 = inj_denominator_1755007751753_99 + inj_in_val_1755007751752_34;
                    end else begin
                        inj_res_1755007751762_461 = inj_denominator_1755007751753_99 - inj_in_val_1755007751752_34;
                    end
                end else if (inj_mode_1755007751762_521 == 3'b011) begin
                    if (inj_denominator_1755007751753_99 < inj_in_val_1755007751752_34) begin
                        inj_res_1755007751762_461 = inj_denominator_1755007751753_99 * inj_in_val_1755007751752_34;
                    end else begin
                        inj_res_1755007751762_461 = inj_denominator_1755007751753_99 / ((inj_in_val_1755007751752_34 == 0) ? 1 : inj_in_val_1755007751752_34);
                    end
                end else if (inj_mode_1755007751762_521 == 3'b100) begin
                    if (inj_denominator_1755007751753_99 != inj_in_val_1755007751752_34) begin
                        if (inj_denominator_1755007751753_99 > inj_in_val_1755007751752_34) inj_res_1755007751762_461 = inj_denominator_1755007751753_99;
                        else inj_res_1755007751762_461 = inj_in_val_1755007751752_34;
                    end else begin
                        inj_res_1755007751762_461 = inj_denominator_1755007751753_99 + inj_in_val_1755007751752_34;
                    end
                end
                else begin
                    inj_res_1755007751762_461 = inj_denominator_1755007751753_99 ^ inj_in_val_1755007751752_34;
                end
            end
            // END: dup_nested_if_ts1755007751763

            name_conflict_example name_conflict_example_inst_1755007751761_9144 (
                .o_out(inj_o_out_1755007751761_631),
                .i_in(inj_i_in_1755007751752_75)
            );
            // BEGIN: GenerateFor_ts1755007751759
            genvar i;
            generate
                for (i = 0; i < 4; i = i + 1) begin : g_loop
                    assign inj_data_out_1755007751759_334[i] = inj_data_in_1755007751759_322[i];
                end
            endgenerate
            // END: GenerateFor_ts1755007751759

            // BEGIN: Module_IfNoneParam_ts1755007751758
            assign inj_out_port_1755007751758_432 = inj_in_val_1755007751755_982;
            // END: Module_IfNoneParam_ts1755007751758

            module_case_write module_case_write_inst_1755007751757_1269 (
                .select_case(inj_select_case_1755007751757_694),
                .case_output_ready(inj_case_output_ready_1755007751757_671),
                .data_case_a(inj_in_val_1755007751752_34),
                .data_case_b(inj_denominator_1755007751753_99)
            );
            nested_macro_expansion nested_macro_expansion_inst_1755007751755_9359 (
                .in_val(inj_in_val_1755007751755_982),
                .out_val(inj_out_val_1755007751755_460)
            );
            packed_struct_module packed_struct_module_inst_1755007751755_1301 (
                .out_byte(inj_out_byte_1755007751755_853),
                .in_packed_data(inj_in_packed_data_1755007751755_117)
            );
            // BEGIN: simple_adder_ts1755007751754
            assign inj_sum_1755007751754_197 = inj_i_in_1755007751752_75 + inj_b_1755007751754_292;
            // END: simple_adder_ts1755007751754

            div_mod_ops div_mod_ops_inst_1755007751753_838 (
                .dividend_mod(inj_dividend_mod_1755007751753_480),
                .divisor_mod(inj_in_val_1755007751752_34),
                .numerator(inj_numerator_1755007751753_234),
                .quotient(inj_quotient_1755007751753_548),
                .remainder(inj_remainder_1755007751753_574),
                .denominator(inj_denominator_1755007751753_99)
            );
            configuration_top configuration_top_inst_1755007751752_6922 (
                .i_in(inj_i_in_1755007751752_75),
                .o_out(inj_o_out_1755007751752_705)
            );
            ModuleGenerateIf ModuleGenerateIf_inst_1755007751752_2404 (
                .in_val(inj_in_val_1755007751752_34),
                .out_val(inj_out_val_1755007751752_33)
            );
        assign intermediate_a_ts1755007751751 = inj_in_vector_1755007751749_932 + 8'd1;
        assign intermediate_b_ts1755007751751 = intermediate_a_ts1755007751751 << 1;
        assign intermediate_c_ts1755007751751 = intermediate_a_ts1755007751751 >> 1;
        assign inj_out_data_1755007751750_980 = intermediate_b_ts1755007751751 | intermediate_c_ts1755007751751;
        // END: simple_comb_ts1755007751751

        // BEGIN: module_selection_ts1755007751749
        always_comb begin
        inj_out_vector_assign_1755007751749_231 = inj_in_vector_1755007751749_932;
        inj_out_bit_select_1755007751749_119 = inj_in_vector_1755007751749_932[inj_in_index_1755007751749_826];
        inj_out_part_select_1755007751749_766 = inj_in_vector_1755007751749_932[inj_in_part_lsb_1755007751749_411 +: 4];
        inj_out_bitwise_ops_1755007751749_266 = inj_in_vector_1755007751749_932 & {8{clk}};
        end
        // END: module_selection_ts1755007751749

    assign processed_wide_ts1755007751749 = inj_wide_in_1755007751749_790 * 2;
    assign inj_upper_byte_out_1755007751749_681 = processed_wide_ts1755007751749[31:24];
    assign inj_lower_byte_out_1755007751749_140 = processed_wide_ts1755007751749[7:0];
    // END: part_select_ops_ts1755007751749
endmodule

