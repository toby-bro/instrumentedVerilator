module mod_sub (
    input wire in_sub,
    output logic out_sub
);
    assign out_sub = in_sub;
endmodule

module snippet (
    input wire clk,
    input wire [2:0] inj_count_in_1755007788376_513,
    input wire reset,
    output wire [2:0] inj_count_out_1755007788376_221,
    output logic inj_out_sub_1755007788375_224
);
    // BEGIN: simple_seq_ts1755007788376
    reg [2:0] counter_reg_ts1755007788376;
    always @(posedge clk or posedge reset) begin
        if (reset) begin
            counter_reg_ts1755007788376 <= 3'b000;
        end else begin
            counter_reg_ts1755007788376 <= inj_count_in_1755007788376_513 + 3'b001;
        end
    end
    assign inj_count_out_1755007788376_221 = counter_reg_ts1755007788376;
    // END: simple_seq_ts1755007788376

    mod_sub mod_sub_inst_1755007788375_9334 (
        .out_sub(inj_out_sub_1755007788375_224),
        .in_sub(clk)
    );
endmodule

