`timescale 1ns / 1ps
module module_multitop_A (
    input logic [7:0] data_in_A,
    output logic [7:0] data_out_A,
    input logic clk_A
);
    logic [7:0] internal_data_A;
    logic common_signal_a;
    logic common_io_name;
    always_comb begin
        internal_data_A = data_in_A + 1;
        data_out_A = internal_data_A;
        common_signal_a = data_in_A[0];
        common_io_name = data_in_A[7];
    end
endmodule
module module_multitop_B (
    input logic [3:0] data_in_B,
    output logic [3:0] data_out_B,
    input logic reset_B
);
    timeunit 10ns;
    timeprecision 1ns;
    logic [3:0] internal_data_B;
    logic common_signal_a;
    always_comb begin
        internal_data_B = data_in_B * 2;
        data_out_B = internal_data_B;
        common_signal_a = data_in_B[0];
    end
endmodule
interface my_simple_interface;
    logic request;
    logic [15:0] address;
    logic acknowledge;
    modport master (output request, output address, input acknowledge);
    modport slave (input request, input address, output acknowledge);
endinterface
module module_interface_ports (
    input logic [7:0] regular_in_if,
    output logic [7:0] regular_out_if,
    output logic common_io_name
);
    my_simple_interface if_instance();
    my_simple_interface if_array_instance[2]();
    logic local_ref_variable;
    always_comb begin
        regular_out_if = regular_in_if;
        if_instance.request = 1'b1;
        if_instance.address = {8'b0, regular_in_if};
        common_io_name = regular_in_if[0];
        if_array_instance[0].request = regular_in_if[1];
        if_array_instance[0].address = {8'b0, regular_in_if};
        if_array_instance[1].request = regular_in_if[2];
        if_array_instance[1].address = {8'b0, regular_in_if};
        local_ref_variable = regular_in_if[0];
    end
endmodule
class MySystemVerilogClass;
    int data_val;
    function new(int initial_val);
        this.data_val = initial_val;
    endfunction
    function int getData();
        return data_val;
    endfunction
    function void setData(int new_val);
        this.data_val = new_val;
    endfunction
endclass
class AnotherSystemVerilogClass;
    string name;
    function new(string n);
        this.name = n;
    endfunction
    function string getName();
        return name;
    endfunction
endclass
package my_custom_package;
    parameter int PACKAGE_ID = 123;
    function automatic int sum_two(int a, int b);
        return a + b;
    endfunction
    class PackageClassWithTime;
        int count;
        function new();
            this.count = 0;
        endfunction
    endclass
endpackage
module module_package_user (
    input logic [15:0] pkg_in_data,
    output logic [15:0] pkg_out_data,
    input logic enable_class_ops
);
    import my_custom_package::*;
    MySystemVerilogClass sv_obj_1;
    AnotherSystemVerilogClass sv_obj_2;
    int local_calc_result;
    string obj_name_str;
    always_comb begin
        if (enable_class_ops) begin
            sv_obj_1 = new(pkg_in_data[7:0]);
            local_calc_result = sv_obj_1.getData() + PACKAGE_ID;
            sv_obj_2 = new("VerilatorTest");
            obj_name_str = sv_obj_2.getName();
        end else begin
            local_calc_result = 0;
            obj_name_str = "";
        end
        pkg_out_data = sum_two(pkg_in_data, local_calc_result);
    end
endmodule
module module_child_level (
    input logic child_input,
    output logic child_output,
    input logic [3:0] child_data_in,
    output logic [3:0] child_data_out
);
    always_comb begin
        child_output = ~child_input;
        child_data_out = child_data_in + 1;
    end
endmodule
module module_parent_hierarchy (
    input logic parent_in,
    output logic parent_out,
    input logic [3:0] parent_data_in,
    output logic [3:0] parent_data_out
);
    logic intermediate_sig_A;
    logic [3:0] intermediate_data_B;
    module_child_level child_inst (
        .child_input(parent_in),
        .child_output(intermediate_sig_A),
        .child_data_in(parent_data_in),
        .child_data_out(intermediate_data_B)
    );
    always_comb begin
        parent_out = intermediate_sig_A;
        parent_data_out = intermediate_data_B;
    end
endmodule
module module_simple_counter (
    input logic clock,
    input logic reset_n,
    output logic [4:0] count_out
);
    logic [4:0] counter_reg;
    always_ff @(posedge clock or negedge reset_n) begin
        if (!reset_n) begin
            counter_reg <= 5'b0;
        end else begin
            counter_reg <= counter_reg + 1;
        end
    end
    assign count_out = counter_reg;
endmodule
module module_data_flipper (
    input logic [7:0] in_val,
    output logic [7:0] out_val
);
    always_comb begin
        out_val = ~in_val;
    end
endmodule
typedef enum logic [1:0] {
    STATE_IDLE,
    STATE_READ,
    STATE_WRITE
} fsm_state_t;
typedef struct packed {
    logic [7:0] addr;
    logic [15:0] data;
    logic        valid;
} packet_t;
module module_complex_types (
    input fsm_state_t current_state_in,
    input packet_t input_packet,
    output fsm_state_t next_state_out,
    output packet_t output_packet
);
    always_comb begin
        next_state_out = current_state_in;
        output_packet.addr = input_packet.addr + 1;
        output_packet.data = input_packet.data;
        output_packet.valid = input_packet.valid;
    end
endmodule
