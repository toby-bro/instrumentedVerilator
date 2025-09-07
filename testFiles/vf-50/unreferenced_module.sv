module unreferenced_module (
    input wire clk,
    input logic [1:0] inj_case_expr_1755538370724_147,
    input wire rst,
    input logic unused_in,
    output logic [4:0] inj_internal_out_1755538370724_838,
    output logic unused_out
);
    // BEGIN: case_full_simple_mod_ts1755538370724
    always @* begin
        (* full *)
        case (inj_case_expr_1755538370724_147)
            2'b00: inj_internal_out_1755538370724_838 = 10;
            2'b01: inj_internal_out_1755538370724_838 = 11;
            2'b10: inj_internal_out_1755538370724_838 = 12;
            default: inj_internal_out_1755538370724_838 = 13;
        endcase
    end
    // END: case_full_simple_mod_ts1755538370724

    assign unused_out = ~unused_in;
endmodule

