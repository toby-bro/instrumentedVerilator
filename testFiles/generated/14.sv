module simple_and_gate (
    input logic in1,
    input logic in2,
    output logic out
);
    assign out = in1 & in2;
endmodule

module snippet #(
    parameter int P_PORT_VAL = 25
) (
    input wire clk,
    input logic [1:0] inj_case_expr_1755004207613_826,
    input logic [3:0] inj_i_addr_arr_1755004207614_113,
    input logic [3:0] inj_i_addr_sel_1755004207614_504,
    input logic [7:0] inj_i_vector_1755004207614_442,
    input logic inj_in2_1755004207615_657,
    input logic [7:0] inj_in2_1755004207616_106,
    input bit [7:0] inj_in_cmd_1755004207613_817,
    input int inj_in_val_1755004207618_956,
    input logic inj_tok_in_1755004207614_777,
    input wire reset,
    output logic [4:0] inj_internal_out_1755004207613_681,
    output logic [7:0] inj_o_array_var_elem_1755004207614_859,
    output logic inj_o_sel_var_bit_1755004207614_841,
    output logic [7:0] inj_o_sum_1755004207617_970,
    output logic inj_out_1755004207615_384,
    output logic [7:0] inj_out_1755004207616_937,
    output bit [3:0] inj_out_status_1755004207613_583,
    output int inj_out_val_1755004207618_187,
    output logic [8:0] inj_out_val_c_l_1755004207616_537,
    output logic [7:0] inj_out_val_d_l_1755004207616_726,
    output logic [7:0] inj_result_m_1755004207619_672,
    output logic inj_tok_out_1755004207614_18
);
    // BEGIN: case_full_simple_mod_ts1755004207613
    // BEGIN: mod_case_standard_ts1755004207614
    // BEGIN: Module_MacroTokens_ts1755004207614
    // BEGIN: HandleOutOfBoundsRead_ts1755004207615
    parameter ARR_SIZE = 4;
    logic [7:0] my_array_ts1755004207615 [0:ARR_SIZE-1];
        // BEGIN: nested_macro_expansion_ts1755004207618
        `define LVL1(x) ((x) + 1)
        `define LVL2(y) `LVL1((y) * 2)
        `define LVL3(z) `LVL2((z) / 3)
        int nested_result_ts1755004207618;
            // BEGIN: split_nested_if_ts1755004207620
            always @(posedge clk) begin
                if (inj_tok_in_1755004207614_777) begin
                    if (inj_in2_1755004207615_657) begin
                        inj_result_m_1755004207619_672 <= inj_i_vector_1755004207614_442;
                    end else begin
                        inj_result_m_1755004207619_672 <= inj_in2_1755004207616_106;
                    end
                end else begin
                    inj_result_m_1755004207619_672 <= my_array_ts1755004207615;
                end
            end
            // END: split_nested_if_ts1755004207620

        always_comb begin
            nested_result_ts1755004207618 = `LVL3(`LVL1(inj_in_val_1755004207618_956));
        end
        assign inj_out_val_1755004207618_187 = nested_result_ts1755004207618;
        // END: nested_macro_expansion_ts1755004207618

        // BEGIN: param_local_port_ts1755004207617
        localparam int LP_BODY_VAL = 125;
        localparam int LP_CALCULATED = P_PORT_VAL + LP_BODY_VAL;
        always_comb begin
            if (reset) begin
                inj_o_sum_1755004207617_970 = 0;
            end else begin
                inj_o_sum_1755004207617_970 = LP_CALCULATED;
            end
        end
        // END: param_local_port_ts1755004207617

        // BEGIN: split_inputs_outputs_only_ts1755004207616
        always @(*) begin
            inj_out_val_c_l_1755004207616_537 = my_array_ts1755004207615 + inj_i_vector_1755004207614_442;
            inj_out_val_d_l_1755004207616_726 = my_array_ts1755004207615 - inj_i_vector_1755004207614_442;
        end
        // END: split_inputs_outputs_only_ts1755004207616

        // BEGIN: bitwise_ops_ts1755004207616
        assign inj_out_1755004207616_937 = (my_array_ts1755004207615 & inj_in2_1755004207616_106) | (~inj_i_vector_1755004207614_442) ^ (my_array_ts1755004207615 << 2) >> 1;
        // END: bitwise_ops_ts1755004207616

        simple_and_gate simple_and_gate_inst_1755004207615_4766 (
            .in1(inj_tok_in_1755004207614_777),
            .in2(inj_in2_1755004207615_657),
            .out(inj_out_1755004207615_384)
        );
    assign my_array_ts1755004207615[0] = 8'd10;
    assign my_array_ts1755004207615[1] = 8'd20;
    assign my_array_ts1755004207615[2] = 8'd30;
    assign my_array_ts1755004207615[3] = 8'd40;
    assign inj_o_sel_var_bit_1755004207614_841 = inj_i_vector_1755004207614_442[inj_i_addr_sel_1755004207614_504];
    assign inj_o_array_var_elem_1755004207614_859 = my_array_ts1755004207615[inj_i_addr_arr_1755004207614_113];
    // END: HandleOutOfBoundsRead_ts1755004207615

    `define PASTE(a,b) a``b
    logic `PASTE(my,_var);
    always_comb begin
        `PASTE(my,_var) = inj_tok_in_1755004207614_777;
        inj_tok_out_1755004207614_18         = `PASTE(my,_var);
    end
    // END: Module_MacroTokens_ts1755004207614

always_comb begin
    case (inj_in_cmd_1755004207613_817)
        8'd0, 8'd1, 8'd2: begin
            inj_out_status_1755004207613_583 = 4'hA;
        end
        8'd3, 8'd4: begin
            inj_out_status_1755004207613_583 = 4'hB;
        end
        default: begin
            inj_out_status_1755004207613_583 = 4'hF;
        end
    endcase
end
    // END: mod_case_standard_ts1755004207614

    always @* begin
        (* full *)
        case (inj_case_expr_1755004207613_826)
            2'b00: inj_internal_out_1755004207613_681 = 10;
            2'b01: inj_internal_out_1755004207613_681 = 11;
            2'b10: inj_internal_out_1755004207613_681 = 12;
            default: inj_internal_out_1755004207613_681 = 13;
        endcase
    end
    // END: case_full_simple_mod_ts1755004207613
endmodule

