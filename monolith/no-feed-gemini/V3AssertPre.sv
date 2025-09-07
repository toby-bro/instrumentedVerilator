module sva_basic_assertions (
    input logic clk,
    input logic rst_n,
    input logic [7:0] data_in,
    output logic assert_property_pass,
    output logic assign_delay_out
);
    logic reset_active = ~rst_n;
    default disable iff (reset_active);
    default clocking default_cb @(posedge clk);
    endclocking
    property p_data_range;
        (data_in inside {[1:100]});
    endproperty
    assert property (p_data_range);
    property p_data_seq;
        @(posedge clk) (data_in > 50) ##2 (data_in < 20);
    endproperty
    assert property (p_data_seq);
    property p_zero_delay;
        @(posedge clk) 1'b1 ##0 1'b1;
    endproperty
    assert property (p_zero_delay);
    logic [7:0] delay_reg;
    assign #5 delay_reg = data_in; 
    assign assign_delay_out = delay_reg[0];
    assign assert_property_pass = 1'b1; 
endmodule
module sva_concurrent_assertions (
    input logic clk,
    input logic enable_bit,
    input logic data_bit,
    output logic rose_out,
    output logic fell_out,
    output logic stable_out,
    output logic past_val_out
);
    property p_rose_check;
        @(posedge clk) $rose(data_bit);
    endproperty
    assert property (p_rose_check);
    assign rose_out = $rose(data_bit);
    property p_fell_check;
        @(posedge clk) $fell(data_bit);
    endproperty
    assert property (p_fell_check);
    assign fell_out = $fell(data_bit);
    property p_stable_check;
        @(posedge clk) $stable(data_bit);
    endproperty
    assert property (p_stable_check);
    assign stable_out = $stable(data_bit);
    property p_past_check;
        @(posedge clk) (enable_bit) |-> ($past(data_bit, 1) != data_bit);
    endproperty
    assert property (p_past_check);
    assign past_val_out = (enable_bit && ($past(data_bit, 1) != data_bit));
    property p_implication_non_consecutive;
        @(posedge clk) (enable_bit) |=> (data_bit);
    endproperty
    assume property (p_implication_non_consecutive);
endmodule
module sva_property_calls (
    input logic clk,
    input logic [7:0] param_data_in,
    input logic check_cond_in,
    output logic prop_call_output
);
    property my_param_prop (input bit [7:0] val_param);
        @(posedge clk) (val_param > 10);
    endproperty
    assert property (my_param_prop(param_data_in));
    property inner_clocked_prop;
        @(posedge clk) (param_data_in > 20);
    endproperty
    property outer_clock_prop;
        @(posedge clk) inner_clocked_prop;
    endproperty
    assert property (outer_clock_prop);
    assign prop_call_output = my_param_prop(check_cond_in ? 8'd50 : 8'd5);
endmodule
module sva_clocking_block_items (
    input logic clk,
    input logic [3:0] addr_in,
    input logic [7:0] data_bus_in,
    output logic [7:0] data_out_port,
    output logic [3:0] addr_out_port
);
    clocking my_device_cb @(posedge clk);
        input #1step data_bus_in; 
        input #2 my_internal_input_var = data_bus_in + addr_in; 
        output #3 addr_out_port; 
        output #10 my_internal_output_var = 8'hAA; 
    endclocking
    assign my_device_cb.data_out_port <= data_bus_in + 1;
    assign my_device_cb.addr_out_port <= addr_in;
    typedef struct packed {
        logic [3:0] field_a;
        logic [3:0] field_b;
    } my_struct_type;
    my_struct_type s_val_in;
    logic [7:0] combined_struct_out;
    clocking struct_cb @(posedge clk);
        input #1step s_val_in;
        output #0 combined_struct_out = s_val_in.field_a + s_val_in.field_b; 
    endclocking
endmodule
module sva_error_cases (
    input logic clk,
    input logic reset_a,
    input logic reset_b,
    input logic cond_val,
    output logic error_status_out
);
    assert property (cond_val); 
    default clocking clk_a @(posedge clk); endclocking
    default clocking clk_b @(negedge clk); endclocking 
    default disable iff (reset_a);
    default disable iff (reset_b); 
    clocking neg_skew_cb @(posedge clk);
        input #-1 cond_val; 
    endclocking
    logic out_clkvar;
    clocking out_read_err_cb @(posedge clk);
        output #0 out_clkvar;
    endclocking
    assert property (@(posedge clk) out_clkvar == 1'b0); 
    logic in_clkvar;
    clocking in_write_err_cb @(posedge clk);
        input #0 in_clkvar;
    endclocking
    assign in_write_err_cb.in_clkvar <= cond_val; 
    property inner_prop_with_disable (input bit disable_sig);
        disable iff (disable_sig) @(posedge clk) 1'b1;
    endproperty
    property outer_prop_with_disable (input bit disable_sig_outer);
        disable iff (disable_sig_outer) inner_prop_with_disable(~disable_sig_outer);
    endproperty
    assert property (outer_prop_with_disable(cond_val)); 
    assign error_status_out = 1'b1; 
endmodule
