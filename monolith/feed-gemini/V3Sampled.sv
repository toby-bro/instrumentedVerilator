module SimpleSampledAssert (
    input logic clk,
    input logic rst_n,
    input logic [7:0] data_in,
    output logic [7:0] data_out
);
    logic [7:0] internal_reg;
    logic [7:0] another_internal_signal;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            internal_reg <= 8'b0;
            another_internal_signal <= 8'b0;
            data_out <= 8'b0;
        end else begin
            internal_reg <= data_in + 1;
            another_internal_signal <= internal_reg * 2;
            data_out <= another_internal_signal;
        end
    end
    assert property ( @(posedge clk) (rst_n) |-> ($sampled(data_in) == data_in && $sampled(internal_reg) < $sampled(data_in) + 2) );
    assert property ( @(posedge clk) (rst_n && $sampled(internal_reg) > 0) |-> ($sampled(another_internal_signal) == $sampled(internal_reg) * 2) );
endmodule
module ComplexSampledLogic (
    input logic clk,
    input logic [3:0] in_a,
    input logic [3:0] in_b,
    output logic [4:0] out_sum
);
    logic [3:0] intermediate_a;
    logic [3:0] intermediate_b;
    logic [4:0] sum_internal;
    localparam START_VAL = 4'd1;
    function automatic logic [4:0] calculate_sum(input logic [3:0] val1, input logic [3:0] val2);
        logic [4:0] f_sum;
        f_sum = val1 + val2 + START_VAL;
        return f_sum;
    endfunction
    always_ff @(posedge clk) begin
        intermediate_a <= in_a;
        intermediate_b <= in_b;
    end
    always_comb begin
        sum_internal = calculate_sum($sampled(intermediate_a), $sampled(intermediate_b));
        out_sum = sum_internal;
    end
    property p_check_output;
        @(posedge clk) ($sampled(intermediate_a) + $sampled(intermediate_b) + START_VAL == $sampled(out_sum));
    endproperty
    assert property (p_check_output);
endmodule
module SampledAssumptionsAndCoverage (
    input wire clk,
    input wire enable_in,
    input wire [2:0] state_val,
    output logic pass_out
);
    localparam MY_CONSTANT = 3'd5;
    logic internal_flag;
    logic [2:0] next_state_val;
    always_ff @(posedge clk) begin : ff_logic_block
        if (enable_in) begin
            internal_flag <= ~internal_flag;
            next_state_val <= state_val + 1;
        end else begin
            internal_flag <= 1'b0;
            next_state_val <= 3'b0;
        end
        pass_out <= internal_flag && (state_val == MY_CONSTANT);
    end
    assume property ( @(posedge clk) ($sampled(enable_in) |-> $sampled(state_val) < MY_CONSTANT) );
    cover property ( @(posedge clk) ($sampled(state_val) == 3'd3 && $sampled(internal_flag)) );
    assert property ( @(posedge clk) ($sampled(state_val) + $sampled(next_state_val) == $sampled(state_val) * 2 + 1) );
endmodule
module NestedSampledLogic (
    input logic clk,
    input logic condition_in,
    input logic [1:0] val_a,
    input logic [1:0] val_b,
    output logic [2:0] result_out
);
    logic [1:0] temp_val;
    logic [2:0] branch_result;
    logic [2:0] final_calc;
    always_ff @(posedge clk) begin : main_ff_block
        temp_val <= val_a;
        if (condition_in) begin : then_branch_block
            branch_result <= $sampled(val_a) + $sampled(val_b);
        end else begin : else_branch_block
            branch_result <= $sampled(val_a) - $sampled(val_b);
        end
        final_calc <= branch_result + $sampled(temp_val);
        result_out <= final_calc;
        assert property (@(posedge clk) $rose(clk) |-> ($sampled(result_out) >= 0));
    end
endmodule
