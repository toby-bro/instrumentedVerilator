module SimpleSubMod (
    input logic [7:0] in_bus,
    output logic [7:0] out_bus,
    input logic in_scalar,
    output logic out_scalar,
    output logic [15:0] out_wide,
    input logic [3:0] in_narrow,
    input logic in_unconnected_check
);
    assign out_bus = in_bus + 8'd1;
    assign out_scalar = ~in_scalar;
    assign out_wide = {8'h00, in_bus};
endmodule
module TopModuleSimpleConnections (
    input logic [7:0] global_in,
    output logic [7:0] global_out_1,
    output logic [7:0] global_out_2,
    output logic global_out_s1,
    output logic [15:0] global_out_w1,
    output logic [3:0] global_out_n1,
    input logic [15:0] wider_signal
);
    logic [7:0] sub_out_bus_wire;
    logic sub_out_scalar_wire;
    logic [15:0] sub_out_wide_wire;
    logic [3:0] temp_narrow_input;
    logic dummy_out_scalar_inst2;
    logic [7:0] dummy_out_bus_inst3;
    logic dummy_out_scalar_inst3;
    logic [15:0] dummy_out_wide_inst3;
    assign temp_narrow_input = wider_signal[7:4];
    SimpleSubMod inst1 (
        .in_bus(global_in),
        .out_bus(sub_out_bus_wire),
        .in_scalar(global_in[0]),
        .out_scalar(sub_out_scalar_wire),
        .out_wide(sub_out_wide_wire),
        .in_narrow(wider_signal[3:0]),
        .in_unconnected_check(1'b0)
    );
    assign global_out_1 = sub_out_bus_wire;
    assign global_out_s1 = sub_out_scalar_wire;
    assign global_out_w1 = sub_out_wide_wire;
    assign global_out_n1 = temp_narrow_input;
    SimpleSubMod inst2 (
        .in_bus(global_in),
        .out_bus(8'hFF),
        .in_scalar(1'b1),
        .out_scalar(dummy_out_scalar_inst2),
        .out_wide({16'hAAAA}),
        .in_narrow(4'h5),
        .in_unconnected_check(1'b0)
    );
    assign global_out_2 = 8'h00;
    SimpleSubMod inst3 (
        .in_bus(wider_signal[7:0]),
        .out_bus(dummy_out_bus_inst3),
        .in_scalar(wider_signal[8]),
        .out_scalar(dummy_out_scalar_inst3),
        .out_wide(dummy_out_wide_inst3),
        .in_narrow(wider_signal[3:0]),
        .in_unconnected_check(1'b0)
    );
endmodule
module ParameterizedSubMod #(parameter WIDTH = 8, NUM_PORTS = 1) (
    input logic [WIDTH-1:0] in_p,
    output logic [WIDTH-1:0] out_p,
    input logic in_arr_p_scalar,
    output logic out_arr_p_scalar,
    input logic [WIDTH-1:0] in_arr_port_arrayed[NUM_PORTS],
    output logic [WIDTH-1:0] out_arr_port_arrayed[NUM_PORTS]
);
    assign out_p = in_p;
    assign out_arr_p_scalar = in_arr_p_scalar;
    genvar i;
    for (i = 0; i < NUM_PORTS; i++) begin : gen_array_ports
        assign out_arr_port_arrayed[i] = in_arr_port_arrayed[i];
    end
endmodule
module TopModuleArrayedInstance (
    input logic [7:0] overall_data_in,
    output logic [7:0] overall_data_out,
    input logic [31:0] wide_bus_for_scalars,
    output logic [3:0] array_output_scalars [3:0]
);
    parameter NUM_INSTANCES = 4;
    parameter PORT_ARRAY_SIZE = 2;
    logic [7:0] input_data_for_instances [NUM_INSTANCES];
    logic [7:0] output_data_from_instances [NUM_INSTANCES];
    logic scalar_in_for_instances [NUM_INSTANCES];
    logic scalar_out_from_instances [NUM_INSTANCES];
    logic [7:0] arrayed_port_in [NUM_INSTANCES] [PORT_ARRAY_SIZE];
    logic [7:0] arrayed_port_out [NUM_INSTANCES] [PORT_ARRAY_SIZE];
    logic [7:0] dummy_out_p_desc[NUM_INSTANCES];
    logic dummy_out_arr_p_scalar_desc[NUM_INSTANCES];
    logic [7:0] dummy_in_arr_port_arrayed_desc[NUM_INSTANCES][PORT_ARRAY_SIZE];
    logic [7:0] dummy_out_arr_port_arrayed_desc[NUM_INSTANCES][PORT_ARRAY_SIZE];
    genvar j;
    for (j = 0; j < NUM_INSTANCES; j++) begin : connect_inputs_prep
        assign input_data_for_instances[j] = overall_data_in + j;
        assign scalar_in_for_instances[j] = wide_bus_for_scalars[j];
        assign arrayed_port_in[j][0] = 8'd10 + j;
        assign arrayed_port_in[j][1] = 8'd20 + j;
    end
    genvar i_asc;
    for (i_asc = 0; i_asc < NUM_INSTANCES; i_asc++) begin : gen_inst_array_asc
        ParameterizedSubMod #(.WIDTH(8), .NUM_PORTS(PORT_ARRAY_SIZE)) inst (
            .in_p(input_data_for_instances[i_asc]),
            .out_p(output_data_from_instances[i_asc]),
            .in_arr_p_scalar(wide_bus_for_scalars[i_asc]),
            .out_arr_p_scalar(scalar_out_from_instances[i_asc]),
            .in_arr_port_arrayed(arrayed_port_in[i_asc]),
            .out_arr_port_arrayed(arrayed_port_out[i_asc])
        );
    end
    genvar i_desc;
    for (i_desc = 0; i_desc < NUM_INSTANCES; i_desc++) begin : gen_inst_array_desc
        ParameterizedSubMod #(.WIDTH(8), .NUM_PORTS(PORT_ARRAY_SIZE)) inst (
            .in_p(input_data_for_instances[i_desc]),
            .out_p(dummy_out_p_desc[i_desc]),
            .in_arr_p_scalar(wide_bus_for_scalars[i_desc]),
            .out_arr_p_scalar(dummy_out_arr_p_scalar_desc[i_desc]),
            .in_arr_port_arrayed(dummy_in_arr_port_arrayed_desc[i_desc]),
            .out_arr_port_arrayed(dummy_out_arr_port_arrayed_desc[i_desc])
        );
    end
    assign overall_data_out = output_data_from_instances[0];
    for (j = 0; j < NUM_INSTANCES; j++) begin : aggregate_scalars
        assign array_output_scalars[j] = scalar_out_from_instances[j] ? 4'hF : 4'h0;
    end
endmodule
interface MySimpleInterface (input logic clk);
    logic data_in;
    logic data_out;
    modport master (input data_out, output data_in, input clk);
    modport slave (input data_in, output data_out, input clk);
endinterface
module InterfaceModule (
    MySimpleInterface.slave ifc_port,
    input logic module_en,
    output logic interface_data_out_copy
);
    assign ifc_port.data_out = ifc_port.data_in & module_en;
    assign interface_data_out_copy = ifc_port.data_out;
endmodule
module TopModuleInterfaceConnections (
    input logic main_clk,
    input logic main_data_in,
    input logic main_enable,
    output logic main_data_out,
    output logic module_ifc_out
);
    MySimpleInterface simple_ifc (.clk(main_clk));
    assign simple_ifc.data_in = main_data_in;
    assign main_data_out = simple_ifc.data_out;
    InterfaceModule inst_ifc (
        .ifc_port(simple_ifc.slave),
        .module_en(main_enable),
        .interface_data_out_copy(module_ifc_out)
    );
endmodule
interface MyArrayedInterface (input logic clk);
    logic [7:0] val;
    modport port_user (input clk, input val);
    modport port_top (input clk, output val);
endinterface
module ModuleWithArrayedIfacePort (
    input logic a_clk,
    MyArrayedInterface.port_user if_array_port[],
    output logic [7:0] sum_out,
    input logic [7:0] dummy_in_for_port
);
    int k;
    logic [7:0] total_sum;
    always_comb begin
        total_sum = 8'd0;
        for (k = 0; k < if_array_port.size(); k++) begin
            total_sum = total_sum + if_array_port[k].val;
        end
        sum_out = total_sum;
    end
endmodule
module ModuleWithSingleIfacePort (
    input logic s_clk,
    MyArrayedInterface.port_user single_if_port,
    output logic [7:0] single_val_out,
    input logic [7:0] dummy_in_for_single_port
);
    assign single_val_out = single_if_port.val;
endmodule
module TopModuleArrayedInterface (
    input logic top_clk,
    input logic [7:0] top_data_in_base,
    output logic [7:0] total_val_out,
    output logic [7:0] selected_val_out,
    input int select_index,
    input logic [7:0] dummy_input_to_top_arrayed_if
);
    parameter NUM_IF_ARRAY = 4;
    MyArrayedInterface if_array [NUM_IF_ARRAY] (.clk(top_clk));
    MyArrayedInterface.port_user local_if_array_modports [NUM_IF_ARRAY];
    genvar m;
    for (m = 0; m < NUM_IF_ARRAY; m++) begin : if_val_assign
        assign if_array[m].val = top_data_in_base + m;
        assign local_if_array_modports[m] = if_array[m].port_user;
    end
    ModuleWithArrayedIfacePort inst_arrayed_if (
        .a_clk(top_clk),
        .if_array_port(local_if_array_modports),
        .sum_out(total_val_out),
        .dummy_in_for_port(dummy_input_to_top_arrayed_if)
    );
    ModuleWithSingleIfacePort inst_single_if_from_array (
        .s_clk(top_clk),
        .single_if_port(if_array[1].port_user),
        .single_val_out(selected_val_out),
        .dummy_in_for_single_port(top_data_in_base)
    );
endmodule
class MyDataHandler;
    logic [7:0] internal_data;
    function new(logic [7:0] initial_val);
        internal_data = initial_val;
    endfunction
    function logic [7:0] process_data(logic [7:0] input_val);
        return internal_data + input_val;
    endfunction
endclass
module ClassInstanceProcessor (
    input logic [7:0] input_val_a,
    input logic [7:0] input_val_b,
    output logic [7:0] output_processed_val,
    input logic [7:0] dummy_input
);
    MyDataHandler handler_obj;
    always_comb begin
        handler_obj = new(input_val_a);
        output_processed_val = handler_obj.process_data(input_val_b);
    end
endmodule
