module PragmaResetDirectives (
    input bit reset_request,
    output bit system_status_clear
);
`ifdef SLANG_PRAGMA
`reset protect diagnostic
`endif
assign system_status_clear = reset_request;
endmodule

module case_unique0_violating_mod (
    input logic [1:0] case_expr,
    output logic [4:0] internal_out
);
    always @* begin
        unique0 casez (case_expr)
            2'b1?: internal_out = 8;
            2'b11: internal_out = 9;  
            2'b?1: internal_out = 10; 
            2'b00: internal_out = 11; 
        endcase
    end
endmodule

module snippet (
    input wire clk,
    input logic [1:0] inj_case_expr_1755007889847_861,
    input logic [15:0] inj_in1_1755007889847_419,
    input logic [7:0] inj_in1_1755007889848_471,
    input logic [15:0] inj_in2_1755007889847_16,
    input logic [7:0] inj_in2_1755007889848_284,
    input logic inj_sel_1755007889847_843,
    input wire reset,
    output logic [4:0] inj_internal_out_1755007889847_165,
    output logic [15:0] inj_out1_1755007889847_529,
    output logic [7:0] inj_out1_1755007889848_147,
    output logic [15:0] inj_out2_1755007889847_459,
    output logic [7:0] inj_out2_1755007889848_546,
    output logic [15:0] inj_quotient_1755007889849_639,
    output logic [7:0] inj_remainder_1755007889849_715,
    output bit inj_system_status_clear_1755007889847_494
);
    // BEGIN: procedural_complex_ts1755007889847
    logic [15:0] temp1_ts1755007889847;
    logic [15:0] temp2_ts1755007889847;
        // BEGIN: ModuleComb_ts1755007889848
        logic [7:0] internal_wire_ts1755007889848;
            // BEGIN: div_mod_ops_ts1755007889849
            assign inj_quotient_1755007889849_639 = (inj_in2_1755007889848_284 == 0) ? 16'hFFFF : (temp1_ts1755007889847 / inj_in2_1755007889848_284); 
            assign inj_remainder_1755007889849_715 = (internal_wire_ts1755007889848 == 0) ? 8'hFF : (inj_in1_1755007889847_419 % internal_wire_ts1755007889848);
            // END: div_mod_ops_ts1755007889849

        assign internal_wire_ts1755007889848 = inj_in1_1755007889848_471 + inj_in2_1755007889848_284;
        always_comb begin
            if (internal_wire_ts1755007889848 > 8'd128) begin
                inj_out1_1755007889848_147 = internal_wire_ts1755007889848 - 1;
            end else begin
                inj_out1_1755007889848_147 = internal_wire_ts1755007889848 + 1;
            end
            inj_out2_1755007889848_546 = internal_wire_ts1755007889848 / 2;
        end
        // END: ModuleComb_ts1755007889848

    always_comb begin
        temp1_ts1755007889847 = (inj_in1_1755007889847_419 + inj_in2_1755007889847_16) * 10;
        if (inj_sel_1755007889847_843) begin
            temp2_ts1755007889847 = temp1_ts1755007889847 ^ (inj_in1_1755007889847_419 >>> 2);
            inj_out1_1755007889847_529 = temp2_ts1755007889847 & inj_in2_1755007889847_16;
        end else begin
            temp2_ts1755007889847 = temp1_ts1755007889847 | (inj_in2_1755007889847_16 <<< 3);
            inj_out1_1755007889847_529 = temp2_ts1755007889847 + inj_in1_1755007889847_419;
        end
        inj_out2_1755007889847_459 = temp1_ts1755007889847 - temp2_ts1755007889847;
    end
    // END: procedural_complex_ts1755007889847

    PragmaResetDirectives PragmaResetDirectives_inst_1755007889847_3175 (
        .reset_request(reset),
        .system_status_clear(inj_system_status_clear_1755007889847_494)
    );
    case_unique0_violating_mod case_unique0_violating_mod_inst_1755007889847_4038 (
        .internal_out(inj_internal_out_1755007889847_165),
        .case_expr(inj_case_expr_1755007889847_861)
    );
endmodule

