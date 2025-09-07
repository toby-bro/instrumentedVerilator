module PortHandler(
    input logic [7:0] in_data_a,
    input logic [3:0] in_data_b,
    input logic       in_clk,
    output logic [15:0] out_result_wide,
    output logic [7:0]  out_result_narrow,
    output logic [0:0]  out_const_driven
);
    (* unconnected_drive = 1'b1 *) input wire in_unconnected_pull1;
    (* unconnected_drive = 1'b0 *) input wire in_unconnected_pull0;
    assign out_result_wide[7:0] = in_data_a;
    logic [15:0] temp_extended_a;
    assign temp_extended_a = in_data_b;
    assign out_result_wide[15:8] = temp_extended_a[15:8];
    logic [3:0] temp_truncated_a;
    assign temp_truncated_a = in_data_a;
    assign out_result_narrow = temp_truncated_a;
    assign out_const_driven = 1'b0;
    class MySimpleClass;
        int value;
        function new(int init_val);
            value = init_val;
        endfunction
        function int get_value();
            return value;
        endfunction
    endclass
    MySimpleClass my_instance;
    always_comb begin
        if (in_clk) begin
            my_instance = new(in_data_a);
            out_result_narrow = my_instance.get_value();
        end else begin
            my_instance = new(0);
            out_result_narrow = my_instance.get_value();
        end
    end
endmodule
module SimpleSub(
    input logic [3:0] sub_in_val,
    output logic [7:0] sub_out_val
);
    assign sub_out_val = {2{sub_in_val[3]}, sub_in_val, 4'b0};
endmodule
module ArrayedInstanceHandler(
    input logic [31:0] parent_bus_in,
    input logic [7:0] parent_single_in,
    output logic [31:0] parent_bus_out,
    output logic [7:0] parent_single_out
);
    SimpleSub sub_insts[4] (
        .sub_in_val (parent_bus_in[4*idx +: 4]),
        .sub_out_val(parent_bus_out[8*idx +: 8])
    );
    SimpleSub sub_inst_desc[3:0] (
        .sub_in_val (parent_bus_in[4*idx +: 4]),
        .sub_out_val(parent_bus_out[8*idx +: 8])
    );
    logic [7:0] input_array_for_select[2];
    assign input_array_for_select[0] = parent_single_in;
    assign input_array_for_select[1] = parent_single_in + 1;
    SimpleSub single_select_inst (
        .sub_in_val(input_array_for_select[0][3:0]),
        .sub_out_val(parent_single_out)
    );
endmodule
interface MyInterface;
    logic req;
    logic [7:0] data;
    modport master (output req, output data);
    modport slave (input req, input data);
endinterface
module InterfaceHandler(
    input logic master_req_in,
    input logic [7:0] master_data_in,
    output logic slave_req_out,
    output logic [7:0] slave_data_out,
    input logic [0:0] clk
);
    MyInterface my_if();
    assign my_if.req = master_req_in;
    assign my_if.data = master_data_in;
    assign slave_req_out = my_if.req;
    assign slave_data_out = my_if.data;
    always_ff @(posedge clk) begin
        my_if.req <= master_req_in;
        my_if.data <= master_data_in + 1;
    end
    (* unconnected_drive = 1'b0 *) MyInterface unused_if();
    logic [15:0] large_bus_output;
    assign large_bus_output[7:0] = my_if.data[7:0];
endmodule
interface MultiIf;
    logic [7:0] value;
    logic [3:0] control;
    modport p (input value, output control);
endinterface
module ArrayedInterfaceHandler(
    input logic [15:0] input_data,
    output logic [7:0] output_control_concat,
    input logic [0:0] clk_if
);
    MultiIf multi_if_array[2]();
    assign multi_if_array[0].value = input_data[7:0];
    assign multi_if_array[1].value = input_data[15:8];
    assign output_control_concat = {multi_if_array[1].control, multi_if_array[0].control};
    MultiIf another_if_array[2]();
    assign another_if_array = multi_if_array;
    logic [3:0] selected_control_dynamic;
    int k_idx_dynamic;
    always_comb begin
        k_idx_dynamic = clk_if ? 1 : 0;
        selected_control_dynamic = multi_if_array[k_idx_dynamic].control;
    end
endmodule
