module CoverageHelper (
    input bit in_h,
    output logic out_h
);
    assign out_h = in_h;
endmodule

module snippet (
    input wire clk,
    input wire [1:0] inj_byte_idx_1755007857775_707,
    input bit inj_in_h_1755007857775_800,
    input wire [31:0] inj_wide_data_1755007857775_858,
    input wire reset,
    output logic inj_out_h_1755007857775_829,
    output reg [7:0] inj_selected_byte_1755007857775_975
);
    // BEGIN: Bit_Manip_ts1755007857775
    always_comb begin
        case (inj_byte_idx_1755007857775_707)
            2'b00: inj_selected_byte_1755007857775_975 = inj_wide_data_1755007857775_858[7:0];
            2'b01: inj_selected_byte_1755007857775_975 = inj_wide_data_1755007857775_858[15:8];
            2'b10: inj_selected_byte_1755007857775_975 = inj_wide_data_1755007857775_858[23:16];
            default: inj_selected_byte_1755007857775_975 = inj_wide_data_1755007857775_858[31:24];
        endcase
    end
    // END: Bit_Manip_ts1755007857775

    CoverageHelper CoverageHelper_inst_1755007857775_5183 (
        .in_h(inj_in_h_1755007857775_800),
        .out_h(inj_out_h_1755007857775_829)
    );
endmodule

