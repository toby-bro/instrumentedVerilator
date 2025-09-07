module MixedLogic (
    input logic async_reset,
    input logic clk,
    input logic comb_in1,
    input logic comb_in2,
    input logic seq_in,
    output logic comb_out,
    output logic seq_out
);
    logic seq_reg;
    logic comb_intermediate;
    always @(posedge clk or negedge async_reset) begin
        if (!async_reset) begin
            seq_reg <= 1'b0;
        end else begin
            seq_reg <= seq_in;
        end
    end
    assign seq_out = seq_reg;
    always @(seq_reg or comb_in1 or comb_in2) begin
        comb_intermediate = (seq_reg & comb_in1) | (~seq_reg & comb_in2);
    end
    assign comb_out = comb_intermediate;
endmodule

module module_assignments_in_loops (
    input logic [2:0] in_shift,
    input logic [7:0] in_val,
    output logic [3:0] out_part,
    output logic [7:0] out_reg
);
    localparam int PART_START = 4;
    localparam int PART_WIDTH = 4;
    logic [7:0] reg_var;
    logic [3:0] part_var;
    always_comb begin
        reg_var  = in_val;
        part_var = 4'h0;
        for (int i = 0; i < 4; i++) begin
            reg_var  = reg_var + i;
            reg_var += (i * 2);
            reg_var <<= in_shift;
            reg_var[i % 8] = (reg_var[i % 8] == 1'b0);
            reg_var[PART_START +: PART_WIDTH] = i[3:0];
        end
        part_var = reg_var[7:4];
    end
    assign out_reg  = reg_var;
    assign out_part = part_var;
endmodule

module snippet (
    input wire clk,
    input logic [1:0] inj_case_expr_1755007829005_947,
    input logic inj_comb_in1_1755007829005_97,
    input logic inj_comb_in2_1755007829005_867,
    input logic [2:0] inj_in_shift_1755007829005_257,
    input logic [7:0] inj_in_val_1755007829005_167,
    input logic inj_seq_in_1755007829005_853,
    input wire reset,
    output logic inj_comb_out_1755007829005_455,
    output logic [4:0] inj_internal_out_1755007829005_598,
    output logic [3:0] inj_out_part_1755007829005_836,
    output logic [7:0] inj_out_reg_1755007829005_90,
    output logic inj_seq_out_1755007829005_645
);
    // BEGIN: case_full_parallel_mod_ts1755007829005
    always @* begin
        (* full, parallel *)
        case (inj_case_expr_1755007829005_947)
            2'b00: inj_internal_out_1755007829005_598 = 1;
            2'b01: inj_internal_out_1755007829005_598 = 2;
            2'b10: inj_internal_out_1755007829005_598 = 3;
            default: inj_internal_out_1755007829005_598 = 4;
        endcase
    end
    // END: case_full_parallel_mod_ts1755007829005

    MixedLogic MixedLogic_inst_1755007829005_8707 (
        .seq_in(inj_seq_in_1755007829005_853),
        .comb_out(inj_comb_out_1755007829005_455),
        .seq_out(inj_seq_out_1755007829005_645),
        .async_reset(reset),
        .clk(clk),
        .comb_in1(inj_comb_in1_1755007829005_97),
        .comb_in2(inj_comb_in2_1755007829005_867)
    );
    module_assignments_in_loops module_assignments_in_loops_inst_1755007829005_2350 (
        .in_shift(inj_in_shift_1755007829005_257),
        .in_val(inj_in_val_1755007829005_167),
        .out_part(inj_out_part_1755007829005_836),
        .out_reg(inj_out_reg_1755007829005_90)
    );
endmodule

