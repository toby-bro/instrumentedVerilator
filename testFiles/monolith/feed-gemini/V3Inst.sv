interface my_simple_if;
  logic req;
  logic [7:0] data;
  modport master(output req, output data);
  modport slave(input req, input data);
endinterface
module sub_mod_basic (
    input logic in_scalar_p,
    input logic [3:0] in_vec_p,
    output logic out_scalar_p,
    output logic [3:0] out_vec_p,
    inout logic io_scalar_p,
    (* unconnected_drive = "pull1" *) input logic pull_up_in_p,
    (* unconnected_drive = "pull0" *) input logic pull_down_in_p,
    my_simple_if.slave s_if_p
);
  logic dummy_pull_up_logic;
  logic dummy_pull_down_logic;
  assign out_scalar_p = in_scalar_p || s_if_p.req;
  assign out_vec_p = in_vec_p;
  assign io_scalar_p = io_scalar_p;
  assign dummy_pull_up_logic = pull_up_in_p;
  assign dummy_pull_down_logic = pull_down_in_p;
endmodule
module mod_port_connection_tests (
    input logic top_in_A,
    input logic [7:0] top_in_Vec,
    output logic top_out_B,
    output logic top_out_C,
    output logic [3:0] top_out_Vec1,
    output logic [3:0] top_out_Vec2,
    output logic [3:0] top_out_Vec3,
    inout logic top_io_main,
    input logic top_unconn_test,
    output logic [3:0] top_out_inst2_vec,
    output logic top_out_inst4_scalar
);
  my_simple_if if_test();
  logic [3:0] const_val_for_input_vec;
  assign const_val_for_input_vec = 4'h0;
  logic const_val_for_input_scalar;
  assign const_val_for_input_scalar = {1'b0, 1'b0}[0];
  logic [3:0] local_out_vec_inst2;
  logic local_out_scalar_inst4;
  sub_mod_basic inst1 (
      .in_scalar_p(top_in_A),
      .in_vec_p(top_in_Vec[3:0]),
      .out_scalar_p(top_out_B),
      .out_vec_p(top_out_Vec1),
      .io_scalar_p(top_io_main),
      .pull_up_in_p(),
      .pull_down_in_p(top_unconn_test),
      .s_if_p(if_test)
  );
  sub_mod_basic inst2 (
      .in_scalar_p(1'b1),
      .in_vec_p(const_val_for_input_vec),
      .out_scalar_p(top_out_C),
      .out_vec_p(local_out_vec_inst2),
      .io_scalar_p(top_io_main),
      .pull_up_in_p(),
      .pull_down_in_p(),
      .s_if_p(if_test)
  );
  sub_mod_basic inst3 (
      .in_scalar_p(top_in_Vec[0]),
      .in_vec_p(4'b0),
      .out_scalar_p(),
      .out_vec_p(top_out_Vec2),
      .io_scalar_p(top_io_main),
      .pull_up_in_p(),
      .pull_down_in_p(),
      .s_if_p(if_test)
  );
  sub_mod_basic inst4 (
      .in_scalar_p(const_val_for_input_scalar),
      .in_vec_p(top_in_Vec[3:0]),
      .out_scalar_p(local_out_scalar_inst4),
      .out_vec_p(top_out_Vec3),
      .io_scalar_p(top_io_main),
      .pull_up_in_p(),
      .pull_down_in_p(),
      .s_if_p(if_test)
  );
  assign if_test.req = top_in_A;
  assign if_test.data = top_in_Vec;
  assign top_out_inst2_vec = local_out_vec_inst2;
  assign top_out_inst4_scalar = local_out_scalar_inst4;
endmodule
module sub_mod_array_element #(parameter WIDTH = 1) (
    input logic [WIDTH-1:0] in_data_p,
    output logic [WIDTH-1:0] out_data_p
);
  assign out_data_p = in_data_p;
endmodule
module mod_array_instantiation_tests (
    input logic [7:0] top_data_in,
    output logic [7:0] top_data_out,
    output logic [3:0] top_scalar_array_out
);
  for (genvar i = 0; i < 4; i++) begin : gen_inst_width2
    sub_mod_array_element #(.WIDTH(2)) inst_array_width2 (
        .in_data_p(top_data_in[i*2 +: 2]),
        .out_data_p(top_data_out[i*2 +: 2])
    );
  end
  for (genvar j = 0; j < 4; j++) begin : gen_inst_width1
    sub_mod_array_element #(.WIDTH(1)) inst_array_width1 (
        .in_data_p(top_data_in[j]),
        .out_data_p(top_scalar_array_out[j])
    );
  end
endmodule
interface my_if_for_array;
  logic cmd;
  logic [15:0] value;
  modport producer (output cmd, output value);
  modport consumer (input cmd, input value);
endinterface
module sub_if_consumer_single (
    my_if_for_array.consumer s_if_port_p,
    output logic [15:0] result_data_p
);
  assign result_data_p = s_if_port_p.value + {16{s_if_port_p.cmd}};
endmodule
module sub_if_consumer_array (
    my_if_for_array.consumer s_if_port_arr_p [2],
    output logic [15:0] total_sum_p
);
  assign total_sum_p = s_if_port_arr_p[0].value + s_if_port_arr_p[1].value;
endmodule
module mod_interface_dearray_tests (
    input logic input_cmd,
    input logic [15:0] input_value,
    output logic [15:0] output_single_result_total,
    output logic [15:0] output_array_sum_result,
    input logic [1:0] non_const_idx_in
);
  my_if_for_array i_single();
  my_if_for_array i_array[2]();
  my_if_for_array i_array_for_cell_test[2]();
  virtual my_if_for_array v_if_single;
  virtual my_if_for_array v_if_array[2];
  assign i_single.cmd = input_cmd;
  assign i_single.value = input_value;
  assign i_array[0].cmd = input_cmd;
  assign i_array[0].value = input_value;
  assign i_array[1].cmd = !input_cmd;
  assign i_array[1].value = input_value + 1;
  assign i_array_for_cell_test[0].cmd = input_cmd;
  assign i_array_for_cell_test[0].value = input_value;
  assign i_array_for_cell_test[1].cmd = !input_cmd;
  assign i_array_for_cell_test[1].value = input_value + 2;
  logic [15:0] output_single_result_inst1;
  sub_if_consumer_single inst_single_if (
      .s_if_port_p(i_single),
      .result_data_p(output_single_result_inst1)
  );
  sub_if_consumer_array inst_array_if (
      .s_if_port_arr_p(i_array),
      .total_sum_p(output_array_sum_result)
  );
  logic [15:0] result_from_array_element_const;
  sub_if_consumer_single inst_array_element_const (
      .s_if_port_p(i_array[1]),
      .result_data_p(result_from_array_element_const)
  );
  logic [15:0] result_from_array_element_non_const_fixed;
  sub_if_consumer_single inst_array_element_non_const (
      .s_if_port_p(i_array[0]),
      .result_data_p(result_from_array_element_non_const_fixed)
  );
  assign output_single_result_total = output_single_result_inst1 + result_from_array_element_const + result_from_array_element_non_const_fixed;
  for (genvar k = 0; k < 2; k++) begin : gen_if_cell_array
      sub_if_consumer_single inst_if_cell_array (
          .s_if_port_p(i_array_for_cell_test[k]),
          .result_data_p()
      );
  end
  assign v_if_single = i_single;
  assign v_if_array = i_array;
  logic [15:0] sliced_val;
  assign sliced_val = i_array[0].value[1:0];
  always_comb begin
    v_if_array[0].value = input_value;
    v_if_array[0].cmd = input_cmd;
  end
endmodule
