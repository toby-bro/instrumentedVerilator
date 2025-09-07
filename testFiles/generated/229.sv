module BindSimpleModule (
    input bit in,
    output bit out
);
    assign out = in;
endmodule

module simple_seq (
    input wire clk,
    input wire [2:0] count_in,
    input wire reset,
    output wire [2:0] count_out
);
    reg [2:0] counter_reg;
    always @(posedge clk or posedge reset) begin
        if (reset) begin
            counter_reg <= 3'b000;
        end else begin
            counter_reg <= count_in + 3'b001;
        end
    end
    assign count_out = counter_reg;
endmodule

module sub_inst_array_mod (
    input logic [7:0] in,
    output logic [7:0] out
);
    assign out = in;
endmodule

module snippet (
    input wire clk,
    input wire [2:0] inj_count_in_1755007830771_558,
    input bit inj_d_in_1755007830771_447,
    input logic [7:0] inj_in_1755007830771_377,
    input logic [1:0] inj_in_val_1755007830771_781,
    input wire reset,
    output wire [2:0] inj_count_out_1755007830771_543,
    output bit inj_d_out_1755007830771_186,
    output logic [7:0] inj_out_1755007830771_860,
    output reg inj_out_res_1755007830771_373
);
    // BEGIN: DummyBindTarget_ts1755007830771
    // BEGIN: case_single_default_after_item_ts1755007830772
    always_comb begin
        inj_out_res_1755007830771_373 = 1'b0;
        case (inj_in_val_1755007830771_781)
            2'b01: inj_out_res_1755007830771_373 = 1'b1;
            default: inj_out_res_1755007830771_373 = 1'b0;
            2'b10: inj_out_res_1755007830771_373 = 1'b1;
        endcase
    end
    // END: case_single_default_after_item_ts1755007830772

    sub_inst_array_mod sub_inst_array_mod_inst_1755007830771_2207 (
        .out(inj_out_1755007830771_860),
        .in(inj_in_1755007830771_377)
    );
    simple_seq simple_seq_inst_1755007830771_7514 (
        .clk(clk),
        .count_in(inj_count_in_1755007830771_558),
        .reset(reset),
        .count_out(inj_count_out_1755007830771_543)
    );
    assign inj_d_out_1755007830771_186 = inj_d_in_1755007830771_447;
    BindSimpleModule u_bind (.in(inj_d_in_1755007830771_447), .out());
    // END: DummyBindTarget_ts1755007830771
endmodule

