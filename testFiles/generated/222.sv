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

module snippet (
    input wire clk,
    input wire [2:0] inj_count_in_1755007828362_849,
    input logic inj_in_a_1755007828361_589,
    input logic inj_in_b_1755007828361_960,
    input wire reset,
    output wire [2:0] inj_count_out_1755007828362_472,
    output logic inj_out_comb_1755007828361_278,
    output logic inj_out_reg_1755007828361_947
);
    // BEGIN: ModClockedWithSimpleAssign_ts1755007828362
    logic internal_reg_ts1755007828362;
        simple_seq simple_seq_inst_1755007828362_9710 (
            .reset(reset),
            .count_out(inj_count_out_1755007828362_472),
            .clk(clk),
            .count_in(inj_count_in_1755007828362_849)
        );
    always @(posedge clk) begin 
    internal_reg_ts1755007828362 <= inj_in_a_1755007828361_589; 
    end
    assign inj_out_comb_1755007828361_278 = inj_in_a_1755007828361_589 ^ inj_in_b_1755007828361_960; 
    always @(posedge clk) begin 
    inj_out_reg_1755007828361_947 <= internal_reg_ts1755007828362 & inj_in_b_1755007828361_960; 
    end
    // END: ModClockedWithSimpleAssign_ts1755007828362
endmodule

