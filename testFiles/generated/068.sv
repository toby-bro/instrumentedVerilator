module Module_ControlFlow (
    input bit clk,
    input logic [7:0] data_in,
    input bit reset_n,
    input logic [2:0] sel_in,
    output reg [7:0] data_out
);
    reg [7:0] temp;
    always_comb begin
        unique case (sel_in)
            3'b000: temp = data_in;
            3'b001: temp = data_in + 1;
            3'b010: temp = data_in - 1;
            default: temp = 8'hAA;
        endcase
    end
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n)
            data_out <= 8'h00;
        else
            data_out <= temp;
    end
endmodule

module PragmaProtectKeyBlock (
    input bit enable_crypto,
    output bit crypto_active
);
`ifdef SLANG_PRAGMA
`protect key
`endif
`ifdef SLANG_PRAGMA
`protect block
`endif
assign crypto_active = enable_crypto;
endmodule

module mod_named_begin (
    input int data_in,
    output int data_out
);
    always_comb begin : my_named_block
        data_out = data_in;
    end
endmodule

module split_multiple_blocking (
    input logic [3:0] data_in_n,
    output logic [3:0] data_out1_n,
    output logic [3:0] data_out2_n
);
    logic [3:0] temp_n;
    always @(*) begin
        temp_n = data_in_n + 1;
        data_out1_n = temp_n * 2;
        data_out2_n = temp_n + 3;
    end
endmodule

module snippet (
    input wire clk,
    input int inj_data_in_1755007774594_332,
    input logic [7:0] inj_data_in_1755007774596_852,
    input logic [3:0] inj_data_in_n_1755007774595_965,
    input bit inj_enable_crypto_1755007774594_685,
    input logic inj_fs_in_target_1755007774594_714,
    input bit [2:0] inj_in_state_case_1755007774595_546,
    input logic [1:0] inj_in_val_1755007774595_728,
    input logic [2:0] inj_sel_in_1755007774596_74,
    input wire reset,
    output bit inj_crypto_active_1755007774594_895,
    output logic [3:0] inj_data_out1_n_1755007774595_383,
    output logic [3:0] inj_data_out2_n_1755007774595_249,
    output int inj_data_out_1755007774594_511,
    output reg [7:0] inj_data_out_1755007774596_514,
    output logic inj_fs_out_target_1755007774594_87,
    output bit inj_out_priority_case_1755007774595_80,
    output reg inj_out_res_1755007774595_500,
    output bit inj_out_unique_case_1755007774595_174
);
    // BEGIN: mod_fixup_target_ts1755007774594
    // BEGIN: mod_case_unique_priority_ts1755007774595
    // BEGIN: case_default_ts1755007774595
    Module_ControlFlow Module_ControlFlow_inst_1755007774596_9347 (
        .sel_in(inj_sel_in_1755007774596_74),
        .data_out(inj_data_out_1755007774596_514),
        .clk(clk),
        .data_in(inj_data_in_1755007774596_852),
        .reset_n(reset)
    );
    always_comb begin
        inj_out_res_1755007774595_500 = 1'b0;
        case (inj_in_val_1755007774595_728)
            2'b01: inj_out_res_1755007774595_500 = 1'b1;
            2'b10: inj_out_res_1755007774595_500 = 1'b0;
            default: inj_out_res_1755007774595_500 = 1'b1;
        endcase
    end
    // END: case_default_ts1755007774595

    split_multiple_blocking split_multiple_blocking_inst_1755007774595_1031 (
        .data_in_n(inj_data_in_n_1755007774595_965),
        .data_out1_n(inj_data_out1_n_1755007774595_383),
        .data_out2_n(inj_data_out2_n_1755007774595_249)
    );
always_comb begin
    inj_out_unique_case_1755007774595_174 = 1'b0;
    unique case (inj_in_state_case_1755007774595_546)
        3'd0: inj_out_unique_case_1755007774595_174 = 1'b0;
        3'd1: inj_out_unique_case_1755007774595_174 = 1'b1;
        3'd2: inj_out_unique_case_1755007774595_174 = 1'b0;
        3'd1: inj_out_unique_case_1755007774595_174 = 1'b1;
        default: inj_out_unique_case_1755007774595_174 = 1'b1;
    endcase
end
always_comb begin
    inj_out_priority_case_1755007774595_80 = 1'b0;
    priority case (inj_in_state_case_1755007774595_546)
        3'd0: inj_out_priority_case_1755007774595_80 = 1'b0;
        3'd1: inj_out_priority_case_1755007774595_80 = 1'b1;
        3'd2: inj_out_priority_case_1755007774595_80 = 1'b0;
        3'd1: inj_out_priority_case_1755007774595_80 = 1'b1;
        default: inj_out_priority_case_1755007774595_80 = 1'b1;
    endcase
end
    // END: mod_case_unique_priority_ts1755007774595

    mod_named_begin mod_named_begin_inst_1755007774594_7399 (
        .data_out(inj_data_out_1755007774594_511),
        .data_in(inj_data_in_1755007774594_332)
    );
    PragmaProtectKeyBlock PragmaProtectKeyBlock_inst_1755007774594_7948 (
        .enable_crypto(inj_enable_crypto_1755007774594_685),
        .crypto_active(inj_crypto_active_1755007774594_895)
    );
    assign inj_fs_out_target_1755007774594_87 = inj_fs_in_target_1755007774594_714;
    // END: mod_fixup_target_ts1755007774594
endmodule

