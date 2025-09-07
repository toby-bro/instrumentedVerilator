module split_case (
    input logic clk_w,
    input logic [7:0] d0_w,
    input logic [7:0] d1_w,
    input logic [7:0] d2_w,
    input logic [7:0] d3_w,
    input logic [1:0] sel_w,
    output logic [7:0] out_w
);
    always @(posedge clk_w) begin
        case (sel_w)
            2'b00: out_w <= d0_w;
            2'b01: out_w <= d1_w;
            2'b10: out_w <= d2_w;
            default: out_w <= d3_w;
        endcase
    end
endmodule

module snippet (
    input wire clk,
    input logic inj_cond1_m_1755004219004_305,
    input logic inj_cond2_m_1755004219004_828,
    input logic [7:0] inj_d0_w_1755004219004_767,
    input logic [7:0] inj_d1_w_1755004219004_757,
    input logic [7:0] inj_d2_w_1755004219004_283,
    input logic [7:0] inj_d3_w_1755004219004_168,
    input logic [1:0] inj_sel_w_1755004219004_186,
    input wire reset,
    output logic [7:0] inj_out_w_1755004219004_386,
    output logic [7:0] inj_result_m_1755004219004_703
);
    // BEGIN: split_nested_if_ts1755004219005
    always @(posedge clk) begin
        if (inj_cond1_m_1755004219004_305) begin
            if (inj_cond2_m_1755004219004_828) begin
                inj_result_m_1755004219004_703 <= inj_d3_w_1755004219004_168;
            end else begin
                inj_result_m_1755004219004_703 <= inj_d0_w_1755004219004_767;
            end
        end else begin
            inj_result_m_1755004219004_703 <= inj_d1_w_1755004219004_757;
        end
    end
    // END: split_nested_if_ts1755004219005

    split_case split_case_inst_1755004219004_1870 (
        .sel_w(inj_sel_w_1755004219004_186),
        .out_w(inj_out_w_1755004219004_386),
        .clk_w(clk),
        .d0_w(inj_d0_w_1755004219004_767),
        .d1_w(inj_d1_w_1755004219004_757),
        .d2_w(inj_d2_w_1755004219004_283),
        .d3_w(inj_d3_w_1755004219004_168)
    );
endmodule

