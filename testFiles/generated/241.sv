module LintAsyncFovIssue (
    input logic clk,
    input logic in_h,
    input logic rst_n,
    output logic out_i
);
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            out_i <= 1'b0;
        end else begin
            out_i <= in_h & out_i;
        end
    end
endmodule

module snippet (
    input wire clk,
    input logic inj_fs_in_target_1755007834774_249,
    input wire [7:0] inj_in_array_data_1755007834774_671,
    input wire [1:0] inj_select_idx_1755007834774_750,
    input wire reset,
    output logic inj_fs_out_target_1755007834774_753,
    output wire [3:0] inj_out_element_1755007834774_960,
    output logic inj_out_i_1755007834775_852
);
    // BEGIN: unpacked_array_module_ts1755007834774
    logic [3:0] data_array_ts1755007834774 [4];
        LintAsyncFovIssue LintAsyncFovIssue_inst_1755007834775_2139 (
            .clk(clk),
            .in_h(inj_fs_in_target_1755007834774_249),
            .rst_n(reset),
            .out_i(inj_out_i_1755007834775_852)
        );
        // BEGIN: mod_fixup_target_ts1755007834774
        assign inj_fs_out_target_1755007834774_753 = inj_fs_in_target_1755007834774_249;
        // END: mod_fixup_target_ts1755007834774

    always @(*) begin
        data_array_ts1755007834774[0] = inj_in_array_data_1755007834774_671[3:0];
        data_array_ts1755007834774[1] = inj_in_array_data_1755007834774_671[7:4];
        data_array_ts1755007834774[2] = 4'd8;
        data_array_ts1755007834774[3] = 4'd12;
    end
    assign inj_out_element_1755007834774_960 = data_array_ts1755007834774[inj_select_idx_1755007834774_750];
    // END: unpacked_array_module_ts1755007834774
endmodule

