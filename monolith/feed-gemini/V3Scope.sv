package my_package;
    function int add_one(input int val);
        return val + 1;
    endfunction
    function automatic int multiply(input int a, input int b);
        return a * b;
    endfunction
endpackage
interface my_interface(input logic clk);
    logic [7:0] data;
    logic valid;
    function int get_data_sum();
        return data + 1;
    endfunction
    modport master(output data, output valid, input clk);
    modport slave(input data, input valid, input clk);
    modport dpi_ports(export function int get_data_sum());
endinterface
module TopModule(
    input logic        clk_i,
    input logic        rst_ni,
    input logic [7:0]  data_in_i,
    output logic [7:0] result_out_o
);
    logic [7:0] internal_reg;
    logic [7:0] next_internal_reg;
    int         counter;
    enum {STATE_IDLE, STATE_ACTIVE} current_state;
    struct packed { logic [3:0] field1; logic [3:0] field2; } my_struct_var;
    logic [7:0] my_alias_output;
    int         loop_sum_from_submodule;
    int         processed_value_from_pkg_class;
    assign next_internal_reg = data_in_i + 1;
    always_ff @(posedge clk_i or negedge rst_ni) begin : seq_block_proc
        if (!rst_ni) begin
            internal_reg <= 8'h00;
            counter <= 0;
            current_state <= STATE_IDLE;
            my_struct_var <= '{field1: 4'h0, field2: 4'h0};
        end else begin
            internal_reg <= next_internal_reg;
            counter <= counter + 1;
            current_state <= STATE_ACTIVE;
            my_struct_var.field1 <= internal_reg[3:0];
            my_struct_var.field2 <= internal_reg[7:4];
            begin : inner_assign_scope
                logic [7:0] local_temp_var;
                local_temp_var = internal_reg;
                if (local_temp_var > 5) begin
                end
            end
        end
    end
    always_comb begin : comb_result_assign
        result_out_o = internal_reg;
    end
    logic [7:0] public_val;
    always_comb begin : public_logic
        public_val = data_in_i + 2;
    end
    SubModule sub_inst (
        .in_a_i(internal_reg),
        .in_b_i(counter),
        .out_sum_o()
    );
    DPI_InterfaceModule dpi_if_inst (
        .clk_i(clk_i),
        .reset_n_i(rst_ni),
        .value_a_i(counter),
        .value_b_o()
    );
    AliasModule alias_inst (
        .in_i(data_in_i),
        .out_o(my_alias_output)
    );
    PackageClassModule pkg_class_inst (
        .clk_i(clk_i),
        .rst_ni(rst_ni),
        .value_i(counter),
        .processed_value_o(processed_value_from_pkg_class)
    );
    ForLoopModule for_loop_inst (
        .clk_i(clk_i),
        .reset_n_i(rst_ni),
        .loop_count_i(counter),
        .sum_o(loop_sum_from_submodule)
    );
endmodule
module AliasModule(
    input wire [7:0] in_i,
    output wire [7:0] out_o
);
    wire [7:0] aliased_wire;
    alias aliased_wire = in_i;
    assign out_o = aliased_wire;
endmodule
module SubModule(
    input logic [7:0] in_a_i,
    input int         in_b_i,
    output logic [15:0] out_sum_o
);
    logic [7:0] local_data;
    logic [15:0] sum_val;
    always_comb begin : comb_logic
        sum_val = in_a_i + in_b_i;
        local_data = in_a_i;
    end
    assign out_sum_o = sum_val;
    property data_always_positive;
        @(posedge TopModule.clk_i) (local_data >= 0);
    endproperty
    assert property (data_always_positive);
    covergroup my_covergroup @(posedge TopModule.clk_i);
        toggle_a: coverpoint in_a_i;
        toggle_b: coverpoint in_b_i;
    endgroup
    my_covergroup cg_inst = new();
    logic [7:0] top_module_data;
    assign top_module_data = TopModule.data_in_i;
    task automatic get_top_data(output logic [7:0] data_o);
        data_o = TopModule.data_in_i;
    endtask
    always_comb begin : task_caller_block
        logic [7:0] temp_data;
        get_top_data(temp_data);
        if (temp_data inside {8'hFF}) begin
        end
    end
endmodule
module PackageClassModule(
    input logic clk_i,
    input logic rst_ni,
    input int   value_i,
    output int  processed_value_o
);
    import my_package::*;
    int package_func_result;
    int class_func_result;
    assign package_func_result = my_package::add_one(value_i);
    assign processed_value_o = package_func_result;
    class MyClass;
        rand int class_member_a;
        int class_member_b;
        function new(int a, int b);
            class_member_a = a;
            class_member_b = b;
        endfunction
        function int get_sum();
            return class_member_a + class_member_b;
        endfunction
        function int get_product();
            return my_package::multiply(class_member_a, class_member_b);
        endfunction
    endclass
    MyClass my_object;
    always_ff @(posedge clk_i or negedge rst_ni) begin : class_inst_block
        if (!rst_ni) begin
            my_object = new(value_i, value_i + 1);
        end else begin
            if (my_object != null) begin
            end
        end
    end
    always_comb begin : class_func_assign_block
        class_func_result = (my_object != null) ? my_object.get_sum() : 0;
    end
endmodule
module DPI_InterfaceModule(
    input logic  clk_i,
    input logic  reset_n_i,
    input int    value_a_i,
    output int   value_b_o
);
    import "DPI-C" function int c_add_one(input int val);
    import "DPI-C" function int c_multiply(input int a, input int b);
    import "DPI-C" function void c_set_value(output int out_val, input int in_val);
    int dpi_result;
    assign dpi_result = c_add_one(value_a_i);
    always_comb begin : dpi_logic
        c_set_value(value_b_o, c_multiply(value_a_i, dpi_result));
    end
    my_interface if_inst(.clk(clk_i));
    always_ff @(posedge clk_i or negedge reset_n_i) begin : interface_drive_block
        if (!reset_n_i) begin
            if_inst.data <= 0;
            if_inst.valid <= 0;
        end else begin
            if_inst.data <= value_a_i[7:0];
            if_inst.valid <= 1;
        end
    end
    int interface_func_call_result;
    always_comb begin : iface_func_call
        interface_func_call_result = if_inst.get_data_sum();
    end
endmodule
module ForLoopModule(
    input logic clk_i,
    input logic reset_n_i,
    input int   loop_count_i,
    output int  sum_o
);
    int current_sum;
    always_ff @(posedge clk_i or negedge reset_n_i) begin : loop_proc
        if (!reset_n_i) begin
            current_sum <= 0;
        end else begin
            for (var int i = 0; i < loop_count_i; i++) begin
                current_sum <= current_sum + i;
            end
        end
    end
    assign sum_o = current_sum;
endmodule
