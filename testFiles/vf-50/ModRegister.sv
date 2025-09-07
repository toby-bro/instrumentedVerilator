module ModRegister (
    input wire clk,
    input logic din,
    input logic [7:0] inj_in_data_1755538551310_295,
    input wire rst,
    output logic dout,
    output logic [7:0] inj_out_sum_1755538551310_520
);
    // BEGIN: simple_for_loop_ts1755538551310
    logic [7:0] sum_ts1755538551310;
    always_comb begin
        sum_ts1755538551310 = 8'h00;
        for (int i = 0; i < 5; i = i + 1) begin
            sum_ts1755538551310 = sum_ts1755538551310 + inj_in_data_1755538551310_295;
        end
        inj_out_sum_1755538551310_520 = sum_ts1755538551310;
    end
    // END: simple_for_loop_ts1755538551310

    always @* begin
        dout = din;
    end
endmodule

