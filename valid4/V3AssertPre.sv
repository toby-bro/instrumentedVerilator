module DefaultAssertionCoverage (
    input logic clk,
    input logic rst_n,
    input logic data_in,
    output logic assert_pass,
    output logic cover_hit
);
    default clocking dp @(posedge clk); endclocking
    default disable iff (!rst_n);
    property p_data_high;
        @(posedge clk) data_in;
    endproperty
    assert property (p_data_high) else assert_pass = 1'b0;
    cover property (p_data_high) cover_hit = 1'b1;
    property p_explicit_disable;
        disable iff (!rst_n) @(posedge clk) data_in;
    endproperty
    assert property (p_explicit_disable);
    sequence s_implicit_context;
        data_in ##1 data_in;
    endsequence
    property p_implicit_context;
        @(posedge clk) s_implicit_context;
    endproperty
    assert property (p_implicit_context) else assert_pass = 1'b0;
    property p_rose_check;
        @(posedge clk) rose(data_in);
    endproperty
    assert property (p_rose_check);
    property p_fell_check;
        @(posedge clk) fell(data_in);
    endproperty
    assert property (p_fell_check);
    property p_stable_check;
        @(posedge clk) stable(data_in);
    endproperty
    assert property (p_stable_check);
    sequence s_past_check;
        data_in ##1 past(data_in, 1);
    endsequence
    property p_past_check;
        @(posedge clk) s_past_check;
    endproperty
    assert property (p_past_check);
    sequence s_multi_delay_check;
        data_in ##1 ##1 data_in;
    endsequence
    property p_multi_delay_check;
        @(posedge clk) s_multi_delay_check;
    endproperty
    assert property (p_multi_delay_check);
    property p_immediate_implication;
        @(posedge clk) data_in |-> data_in;
    endproperty
    assert property (p_immediate_implication);
    always_comb begin
        assert_pass = 1'b1;
        cover_hit = 1'b0;
    end
endmodule
module ClockingBlockItems (
    input logic clk,
    input logic reset_n,
    input logic [7:0] data_bus_in,
    input logic status_in_ctrl,
    input logic config_in_ctrl,
    output logic [7:0] data_bus_out,
    output logic result_out_val,
    output logic status_out_val
);
    clocking cb @(posedge clk);
        input #1step data_bus_in;
        input #0 status_in_ctrl;
        input #2 config_in_ctrl;
        output #0 data_bus_out;
        output #1 result_out_val;
        output #2 status_out_val;
    endclocking
    logic [7:0] internal_data_reg;
    logic internal_result_reg;
    logic internal_status_reg;
    always_ff @(posedge clk) begin : ff_block
        if (!reset_n) begin
            internal_data_reg <= 8'b0;
            internal_result_reg <= 1'b0;
            internal_status_reg <= 1'b0;
        end else begin
            internal_data_reg <= cb.data_bus_in + 1;
            internal_result_reg <= cb.config_in_ctrl;
            internal_status_reg <= cb.status_in_ctrl;
            cb.data_bus_out <= internal_data_reg;
            cb.result_out_val <= internal_result_reg;
            cb.status_out_val <= internal_status_reg;
        end
    end
    assign data_bus_out = internal_data_reg;
    assign result_out_val = internal_result_reg;
    assign status_out_val = internal_status_reg;
endmodule
module PropertySubstitutionTest (
    input logic clk,
    input logic reset,
    input logic data_a,
    input logic data_b,
    output logic prop_success
);
    default clocking dp @(posedge clk); endclocking
    sequence s_sub_inner (val_in);
        val_in ##1 !val_in;
    endsequence
    property p_sub_inner (val_in);
        @(posedge clk) s_sub_inner(val_in);
    endproperty
    property p_sub_outer (param_a, param_b);
        @(posedge clk) param_a |-> p_sub_inner(param_b);
    endproperty
    assert property (p_sub_outer(data_a, data_b)) else prop_success = 1'b0;
    property p_inner_has_disable (en_cond);
        disable iff (!en_cond) @(posedge clk) data_a;
    endproperty
    property p_call_inner_has_disable (trigger);
        @(posedge clk) trigger |-> p_inner_has_disable(trigger);
    endproperty
    assert property (p_call_inner_has_disable(data_a)) else prop_success = 1'b0;
    property p_outer_and_inner_disable_error;
        disable iff (reset) @(posedge clk) p_inner_has_disable(data_b);
    endproperty
    assert property (p_outer_and_inner_disable_error) else prop_success = 1'b0;
    property p_inner_no_disable (val);
        @(posedge clk) val;
    endproperty
    property p_outer_moves_disable (trigger);
        disable iff (!trigger) @(posedge clk) p_inner_no_disable(data_b);
    endproperty
    assert property (p_outer_moves_disable(data_a)) else prop_success = 1'b0;
    property p_inner_has_clock (val);
        @(posedge clk) val;
    endproperty
    property p_outer_and_inner_clock_warn;
        @(negedge clk) p_inner_has_clock(data_a);
    endproperty
    assert property (p_outer_and_inner_clock_warn) else prop_success = 1'b0;
    property p_inner_no_explicit_clock (val);
        val;
    endproperty
    property p_outer_moves_clock (trigger);
        @(posedge clk) trigger |-> p_inner_no_explicit_clock(data_a);
    endproperty
    assert property (p_outer_moves_clock(data_b)) else prop_success = 1'b0;
    always_comb begin
        prop_success = 1'b1;
    end
endmodule
module MultipleDefaultErrorTest (
    input logic clk_a,
    input logic clk_b,
    input logic reset_a,
    input logic reset_b,
    output logic dummy_out
);
    default clocking dpa @(posedge clk_a); endclocking
    default clocking dpb @(posedge clk_b); endclocking
    default disable iff (reset_a);
    default disable iff (reset_b);
    always_comb begin
        dummy_out = 1'b0;
    end
endmodule
module AssignmentAndDelayContext (
    input logic clk,
    input logic enable_val,
    input logic [3:0] value_in,
    output logic [3:0] value_out,
    output logic [3:0] delayed_value_out
);
    logic [3:0] reg_val;
    logic [3:0] delayed_reg_val;
    logic [3:0] intra_delayed_val;
    always_comb begin
        if (enable_val) begin
            reg_val = value_in;
        end else begin
            reg_val = 4'b0;
        end
        value_out = reg_val;
    end
    always_ff @(posedge clk) begin
        delayed_reg_val <= reg_val;
        delayed_value_out = delayed_reg_val;
    end
    always_ff @(posedge clk) begin
        intra_delayed_val <= #1 value_in;
    end
endmodule
module ZeroCycleDelayProperty (
    input logic clk,
    input logic data_val,
    output logic assertion_failed
);
    default clocking dp @(posedge clk); endclocking
    sequence s_zero_delay;
        data_val ##0 data_val;
    endsequence
    property p_zero_delay;
        @(posedge clk) s_zero_delay;
    endproperty
    assert property (p_zero_delay) else assertion_failed = 1'b1;
    always_comb assertion_failed = 1'b0;
endmodule
module NoDefaultClockingError (
    input logic clk_in,
    input logic enable_in,
    output logic error_out
);
    sequence s_delay_no_default_clk;
        enable_in ##1 enable_in;
    endsequence
    property p_delay_no_default_clk;
        @(posedge clk_in) s_delay_no_default_clk;
    endproperty
    assert property (p_delay_no_default_clk) else error_out = 1'b1;
    always_comb error_out = 1'b0;
endmodule
