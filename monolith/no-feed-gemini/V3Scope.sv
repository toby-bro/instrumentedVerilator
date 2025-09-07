package MyPackage;
    parameter PKG_OFFSET = 10;
    function automatic int pkg_add_offset(int val);
        return val + PKG_OFFSET;
    endfunction
    task automatic pkg_sub_offset(input int val, output int res);
        res = val - PKG_OFFSET;
    endtask
endpackage
import "DPI-C" function int c_add(int a, int b);
class MyDataProcessor;
    rand int processed_value;
    int internal_counter;
    function new();
        internal_counter = 0;
    endfunction
    function int process(int input_data);
        int local_temp_var;
        local_temp_var = input_data * 2;
        processed_value = local_temp_var + internal_counter;
        internal_counter++;
        return processed_value;
    endfunction
endclass
interface MyInterface (input bit clk);
    logic [7:0] data;
    logic [7:0] result;
    function automatic int add_one(int val);
        return val + 1;
    endfunction
    modport Master (
        input data,
        output result,
        export function add_one
    );
    modport Slave (
        output data,
        input result
    );
endinterface
module BasicProcAndAssigns (
    input logic [7:0] in_a,
    input logic [7:0] in_b,
    output logic [8:0] out_sum,
    output logic [7:0] out_diff,
    output logic       out_flag
);
    logic [7:0] internal_reg;
    logic       temp_flag;
    assign out_sum = in_a + in_b;
    always_comb begin
        if (in_a > in_b) begin
            out_diff = in_a - in_b;
            temp_flag = 1'b1;
        end else begin
            out_diff = in_b - in_a;
            temp_flag = 1'b0;
        end
    end
    always_ff @(posedge out_sum[0]) begin
        internal_reg <= in_a;
        out_flag <= temp_flag;
    end
endmodule
module ClassUsageModule (
    input logic [15:0] data_in,
    input logic        enable,
    output logic [31:0] data_out,
    output logic        status_out
);
    MyDataProcessor dp_inst;
    logic [31:0] current_data;
    logic        is_valid;
    always_comb begin
        if (dp_inst == null) begin
            dp_inst = new();
        end
        if (enable) begin
            current_data = dp_inst.process(data_in);
            is_valid = (current_data != 0);
        end else begin
            current_data = 0;
            is_valid = 0;
        end
    end
    assign data_out = current_data;
    assign status_out = is_valid;
endmodule
module FuncTaskDPI (
    input  int in_a,
    input  int in_b,
    output int out_c,
    output int out_d
);
    function automatic int multiply_by_three(int val);
        return val * 3;
    endfunction
    task automatic calculate_sum_and_diff(input int val1, input int val2, output int sum, output int diff);
        sum = val1 + val2;
        diff = val1 - val2;
    endtask
    int sum_val;
    int diff_val;
    int dpi_result;
    always_comb begin
        dpi_result = c_add(in_a, in_b);
        out_c = multiply_by_three(dpi_result);
        calculate_sum_and_diff(in_a, in_b, sum_val, diff_val);
        out_d = sum_val + diff_val;
    end
endmodule
module SubModule (
    input  logic [3:0] sub_in,
    output logic [3:0] sub_out
);
    logic [3:0] internal_var;
    assign internal_var = sub_in + 1;
    assign sub_out = internal_var;
endmodule
module HierarchicalAccess (
    input  logic [3:0] top_in,
    output logic [3:0] top_out
);
    SubModule sm_inst ( .sub_in(top_in), .sub_out(top_out_internal) );
    logic [3:0] top_out_internal;
    logic [3:0] x_ref_value;
    assign x_ref_value = sm_inst.internal_var;
    assign top_out = top_out_internal + x_ref_value;
endmodule
module VerilatorExtensions (
    input logic clk,
    input logic reset,
    input logic [7:0] data,
    output logic [7:0] output_val
);
    logic [7:0] internal_data;
    always_public @(posedge clk or posedge reset) begin
        if (reset) begin
            internal_data <= 8'b0;
        end else begin
            internal_data <= data;
        end
    end
    covergroup my_covergroup @(posedge clk);
        coverpoint data {
            bins low = {0,1};
            bins high = {[254:255]};
            bins mid = {[100:150]};
        }
    endgroup
    my_covergroup cg_inst = new();
    assign output_val = internal_data;
endmodule
module AliasAndModport (
    input  logic       in_signal,
    input  logic [7:0] modport_val,
    output logic       aliased_out,
    output logic [7:0] modport_result
);
    logic internal_logic;
    logic temp_alias_target;
    assign alias aliased_out = temp_alias_target;
    always_comb begin
        temp_alias_target = in_signal;
    end
    MyInterface if_inst (.clk(1'b0));
    logic [7:0] modport_processed_val;
    always_comb begin
        if_inst.Master.data = modport_val;
        modport_processed_val = if_inst.Master.add_one(if_inst.Master.data);
        if_inst.Master.result = modport_processed_val;
    end
    assign modport_result = if_inst.result;
endmodule
module PackageUsage (
    input  int pkg_in_a,
    input  int pkg_in_b,
    output int pkg_out_sum,
    output int pkg_out_diff
);
    import MyPackage::*;
    int temp_sum;
    int temp_diff;
    always_comb begin
        temp_sum = pkg_add_offset(pkg_in_a);
        MyPackage::pkg_sub_offset(pkg_in_b, temp_diff);
        pkg_out_sum = temp_sum + pkg_in_b;
        pkg_out_diff = temp_diff + pkg_in_a;
    end
endmodule
module ScopeTestAssignVarScope (
    input logic in_data,
    output logic out_flag
);
    always_comb begin : named_block_proc
        int local_var_in_proc_block = 5;
        if (in_data) begin : inner_block
            static int static_var_in_inner;
            static_var_in_inner = local_var_in_proc_block + 1;
            out_flag = (static_var_in_inner > 0);
        end else begin
            out_flag = 1'b0;
        end
    end
endmodule
