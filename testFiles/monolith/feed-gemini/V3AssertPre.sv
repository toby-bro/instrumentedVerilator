module ClockedAssertions (
    input clk,
    input rst_n,
    input bit data_in,
    output bit data_out
);
    logic [7:0] count;
    logic prev_data_in;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            count <= 8'd0;
            data_out <= 1'b0;
            prev_data_in <= 1'b0;
        end else begin
            count <= count + 8'd1;
            data_out <= data_in;
            prev_data_in <= data_in;
        end
    end
    property p_rose_data;
        @(posedge clk) $rose(data_in);
    endproperty
    assert property (p_rose_data);
    property p_fell_data;
        @(posedge clk) $fell(data_in);
    endproperty
    assert property (p_fell_data);
    property p_past_data;
        @(posedge clk) (data_in == !$past(data_in));
    endproperty
    assert property (p_past_data);
    property p_stable_data;
        @(posedge clk) $stable(data_in);
    endproperty
    assert property (p_stable_data);
    property p_implication_covered;
        @(posedge clk) (data_in |-> data_out);
    endproperty
    cover property (p_implication_covered);
    logic disable_cond;
    assign disable_cond = (count == 8'd50);
    property p_assert_with_disable;
        @(posedge clk) disable iff (disable_cond) (data_in |=> data_out);
    endproperty
    assert property (p_assert_with_disable);
endmodule
module ClockingFeatures (
    input sys_clk,
    input reset_n,
    input logic [3:0] input_data,
    output logic [3:0] output_sig,
    input logic [3:0] input_sig_q,
    output logic [3:0] output_with_delay,
    output logic bit_out_sel,
    input bit zero_skew_input,
    output bit zero_skew_output
);
    logic input_bit_sel_internal;
    assign input_bit_sel_internal = input_sig_q[0];
    clocking my_cb @(posedge sys_clk);
        input #1step input_data;
        output #2 output_with_delay;
        input #3 input_sig_q;
        input #1step input_bit_sel_internal;
        input #0 zero_skew_input;
    endclocking
    logic [3:0] sampled_input_data_reg;
    always_ff @(posedge sys_clk or negedge reset_n) begin
        if (!reset_n)
            sampled_input_data_reg <= '0;
        else
            sampled_input_data_reg <= my_cb.input_data;
    end
    assign output_sig = sampled_input_data_reg;
    always_ff @(posedge sys_clk or negedge reset_n) begin
        if (!reset_n)
            my_cb.output_with_delay <= '0;
        else
            my_cb.output_with_delay <= input_data;
    end
    logic bit_out_sel_reg;
    always_ff @(posedge sys_clk or negedge reset_n) begin
        if (!reset_n)
            bit_out_sel_reg <= 1'b0;
        else
            bit_out_sel_reg <= my_cb.input_bit_sel_internal;
    end
    assign bit_out_sel = bit_out_sel_reg;
    logic zero_skew_output_reg;
    always_ff @(posedge sys_clk or negedge reset_n) begin
        if (!reset_n)
            zero_skew_output_reg <= 1'b0;
        else
            zero_skew_output_reg <= my_cb.zero_skew_input;
    end
    assign zero_skew_output = zero_skew_output_reg;
endmodule
module DefaultSettings (
    input main_clk,
    input reset_assert,
    input bit enable_feature,
    input bit specific_condition,
    output bit default_assert_out
);
    default clocking default_cb @(posedge main_clk); endclocking
    default disable iff (reset_assert);
    property p_default_assert;
        (enable_feature |=> !specific_condition);
    endproperty
    assert property (@(default_cb) p_default_assert);
    property p_explicit_disable;
        disable iff (specific_condition) (enable_feature |=> 1'b1);
    endproperty
    assert property (@(default_cb) p_explicit_disable);
    property p_inner_with_disable_for_test (bit inner_cond);
        @(default_cb) disable iff (inner_cond) (enable_feature);
    endproperty
    assert property (@(default_cb) p_inner_with_disable_for_test(specific_condition));
    assign default_assert_out = enable_feature && specific_condition;
endmodule
module PropertyCalls (
    input clk_p,
    input bit arg_a,
    input bit arg_b,
    output bit out_val_pc,
    input bit outer_disable_cond
);
    logic [7:0] counter_pc;
    assign out_val_pc = arg_a & arg_b;
    always_ff @(posedge clk_p) begin
        counter_pc <= counter_pc + 8'd1;
    end
    property my_param_prop (bit p_a, bit p_b);
        @(posedge clk_p) (p_a and p_b);
    endproperty
    assert property (my_param_prop(arg_a, arg_b));
    property prop_with_internal_control (bit c);
        @(posedge clk_p) disable iff (c) (counter_pc > 8'd10);
    endproperty
    logic call_disable_cond;
    assign call_disable_cond = (counter_pc < 8'd5);
    assert property (@(posedge clk_p) prop_with_internal_control(call_disable_cond));
    property prop_inner_only_disable (bit cond_in);
        @(posedge clk_p) disable iff (cond_in) (arg_a);
    endproperty
    property prop_outer_disable (bit cond_inner, bit cond_outer);
        prop_inner_only_disable(cond_inner || cond_outer);
    endproperty
    assert property (@(posedge clk_p) prop_outer_disable(call_disable_cond, outer_disable_cond));
endmodule
module SequenceDelays (
    input s_clk,
    input bit trigger_s,
    output bit asserted_s
);
    logic [7:0] delay_counter;
    assign asserted_s = (delay_counter > 8'd0);
    default clocking seq_cb @(posedge s_clk); endclocking
    always_ff @(posedge s_clk) begin
        if (trigger_s) begin
            delay_counter <= 8'd10;
        end else if (delay_counter > 0) begin
            delay_counter <= delay_counter - 1;
        end
    end
    sequence s_delayed_trigger;
        trigger_s ##5 !trigger_s;
    endsequence
    assert property (@(posedge s_clk) s_delayed_trigger);
    logic reg_a, reg_b;
    always_ff @(posedge s_clk) begin
        reg_a <= trigger_s;
        reg_b = reg_a;
    end
endmodule
