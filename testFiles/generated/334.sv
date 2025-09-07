interface my_if;
    logic [7:0] data;
    logic ready;
    logic valid;
    modport FullAccess (input data, output ready, output valid);
    modport AccessIn (output data, output valid, input ready);
    modport AccessOut (input data, input valid, output ready);
endinterface
module snippet (
    input wire clk,
    input logic [7:0] inj_in_value_1755007866449_134,
    input wire reset,
    output logic inj_out_data_q_1755007866449_907
);
    // BEGIN: module_assign_nonblocking_ts1755007866449
    my_if vif_inst();
    logic [7:0] data_q_ts1755007866449;
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            vif_inst.data <= 8'h0;
            data_q_ts1755007866449 <= 8'h0;
        end else begin
            vif_inst.data <= inj_in_value_1755007866449_134;
            data_q_ts1755007866449 <= vif_inst.data;
        end
    end
    assign inj_out_data_q_1755007866449_907 = data_q_ts1755007866449;
    // END: module_assign_nonblocking_ts1755007866449
endmodule

