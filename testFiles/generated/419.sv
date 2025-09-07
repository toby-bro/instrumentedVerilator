module snippet (
    input wire clk,
    input logic [7:0] inj_data_in_1755007894462_991,
    input logic [2:0] inj_in_val_1755007894462_440,
    input wire reset,
    output logic [7:0] inj_data_out_1755007894462_930,
    output logic inj_is_even_1755007894462_200,
    output reg inj_out_res_1755007894462_755
);
    // BEGIN: FunctionTaskMod_ts1755007894462
    function automatic bit check_even(input logic [7:0] v);
        check_even = ~v[0];
    endfunction
    task automatic dummy_task(input logic [7:0] v);
        int tmp_ts1755007894462;
        tmp_ts1755007894462 = v;
    // BEGIN: SequentialLogic_ts1755007894463
    logic [7:0] internal_reg_ts1755007894463;
    always @(posedge clk or negedge reset) begin
        if (~reset) begin
            internal_reg_ts1755007894463 <= 8'h00;
        end else begin
            internal_reg_ts1755007894463 <= inj_data_in_1755007894462_991;
        end
    end
    assign inj_data_out_1755007894462_930 = internal_reg_ts1755007894463;
    // END: SequentialLogic_ts1755007894463

    // BEGIN: casez_xz_ts1755007894462
    always_comb begin
        inj_out_res_1755007894462_755 = 1'b0;
        casez (inj_in_val_1755007894462_440)
            3'b1??: inj_out_res_1755007894462_755 = 1'b1;
            3'b0z?: inj_out_res_1755007894462_755 = 1'b0;
            default: inj_out_res_1755007894462_755 = 1'b1;
        endcase
    end
    // END: casez_xz_ts1755007894462

    endtask
    assign inj_is_even_1755007894462_200 = check_even(inj_data_in_1755007894462_991);
    // END: FunctionTaskMod_ts1755007894462
endmodule

