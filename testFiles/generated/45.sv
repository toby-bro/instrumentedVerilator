module sequential_always_assign (
    input logic clk,
    input logic [7:0] in,
    output logic [7:0] out
);
    always @(posedge clk) begin
        out <= in;
    end
endmodule

module snippet (
    input wire clk,
    input logic [1:0] inj_case_expr_1755004218631_812,
    input logic [3:0] inj_case_inside_val_1755004218631_251,
    input logic inj_condition_h_1755004218632_916,
    input bit [7:0] inj_in1_1755004218630_265,
    input bit [7:0] inj_in2_1755004218630_223,
    input logic [7:0] inj_in_1755004218631_312,
    input wire reset,
    output logic [4:0] inj_internal_out_1755004218631_520,
    output bit [7:0] inj_out1_1755004218630_583,
    output bit [7:0] inj_out2_1755004218630_756,
    output logic [7:0] inj_out_1755004218631_271,
    output logic [7:0] inj_out_reg_h_1755004218632_954
);
    // BEGIN: comb_simple_ts1755004218631
    // BEGIN: case_priority_casex_complex_mod_ts1755004218632
    // BEGIN: split_if_only_then_ts1755004218632
    always @(posedge clk) begin
        if (inj_condition_h_1755004218632_916) begin
            inj_out_reg_h_1755004218632_954 <= inj_in_1755004218631_312;
        end
    end
    // END: split_if_only_then_ts1755004218632

    always @* begin
        priority casex ({inj_case_expr_1755004218631_812, inj_case_inside_val_1755004218631_251[1:0]})
            4'b1???: inj_internal_out_1755004218631_520 = 24;
            4'b?1??: inj_internal_out_1755004218631_520 = 25;  
            4'b??1?: inj_internal_out_1755004218631_520 = 26;  
            4'b???1: inj_internal_out_1755004218631_520 = 27;  
            4'b0000: inj_internal_out_1755004218631_520 = 28;  
            default: inj_internal_out_1755004218631_520 = 29;
        endcase
    end
    // END: case_priority_casex_complex_mod_ts1755004218632

    sequential_always_assign sequential_always_assign_inst_1755004218631_4784 (
        .clk(clk),
        .in(inj_in_1755004218631_312),
        .out(inj_out_1755004218631_271)
    );
    always @* begin
        inj_out1_1755004218630_583 = inj_in1_1755004218630_265 & inj_in2_1755004218630_223;
        inj_out2_1755004218630_756 = inj_in1_1755004218630_265 | inj_in2_1755004218630_223;
    end
    // END: comb_simple_ts1755004218631
endmodule

