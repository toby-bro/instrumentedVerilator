class MyBaseClass;
  logic [7:0] data;
  function new();
    this.data = 8'hAA;
  endfunction
  function int getData();
    return this.data;
  endfunction
endclass
class MyDerivedClass extends MyBaseClass;
  int counter;
  function new();
    super.new();
    this.counter = 0;
  endfunction
  function void increment_counter();
    this.counter++;
  endfunction
  function int getData();
    return super.getData() + this.counter;
  endfunction
endclass
module ClassHandlingMod (
  input logic enable_i,
  output int sum_data_o
);
  MyBaseClass base_obj;
  MyDerivedClass derived_obj;
  MyBaseClass base_array[2]; 
  always_comb begin
    sum_data_o = 0;
    if (enable_i) begin
      base_obj = new();
      derived_obj = new();
      base_obj.data = 8'h55;
      derived_obj.increment_counter(); 
      sum_data_o = base_obj.getData() + derived_obj.getData(); 
      base_array[0] = new();
      base_array[1] = new MyDerivedClass(); 
      base_array[0].data = 8'h10;
      base_array[1].data = 8'h20; 
      sum_data_o += base_array[0].getData(); 
      sum_data_o += base_array[1].getData(); 
    end
  end
endmodule
module LeafMod (
  input logic [3:0] leaf_in,
  output logic [3:0] leaf_out
);
  always_comb begin
    leaf_out = leaf_in + 1;
  end
endmodule
module HierarchyMod (
  input logic [7:0] hierarchy_in,
  output logic [7:0] hierarchy_out
);
  LeafMod leaf_instance (
    .leaf_in (hierarchy_in[3:0]),
    .leaf_out(hierarchy_out[3:0])
  );
  always_comb begin
    hierarchy_out[7:4] = hierarchy_in[7:4] * 2;
  end
endmodule
module StructAndPackedTypesMod (
  input logic [15:0] input_val_i,
  output logic [31:0] output_val_o
);
  typedef struct packed {
    logic [7:0] field_a;
    logic [7:0] field_b;
  } my_packed_struct_t;
  typedef struct {
    int id;
    my_packed_struct_t data_fields;
    logic [3:0] status_flags [2]; 
  } my_unpacked_struct_t;
  my_unpacked_struct_t config_data;
  my_unpacked_struct_t configs_array[4]; 
  always_comb begin
    config_data.id = input_val_i;
    config_data.data_fields.field_a = input_val_i[7:0];
    config_data.data_fields.field_b = input_val_i[15:8];
    config_data.status_flags[0] = 4'b1010;
    config_data.status_flags[1] = 4'b0101;
    configs_array[0] = config_data;
    configs_array[1].id = input_val_i + 1;
    configs_array[1].data_fields.field_a = 8'hF0;
    configs_array[1].data_fields.field_b = 8'h0F;
    configs_array[1].status_flags[0] = 4'b0001;
    configs_array[1].status_flags[1] = 4'b0010;
    output_val_o = config_data.id + config_data.data_fields.field_a +
                   config_data.data_fields.field_b +
                   configs_array[0].status_flags[0] + configs_array[1].data_fields.field_a;
    my_unpacked_struct_t temp_struct;
    temp_struct.id = 100;
    temp_struct.data_fields.field_a = 50;
    output_val_o += temp_struct.id + temp_struct.data_fields.field_a;
  end
endmodule
module DPIHandlingMod (
  input int in_arg_a_i,
  input real in_arg_b_i,
  output int out_ret_val_o
);
  import "DPI-C" function int c_add_int_real(int a, real b);
  import "DPI-C" function string c_get_version_string();
  import "DPI-C" context function int c_context_func(input bit [3:0] in_packed_arr[2]);
  import "DPI-C" function void c_log_message(string msg);
  import "DPI-C" function logic [63:0] c_process_longint_array(input longint data_in[]);
  export "DPI-C" function sv_process_data;
  function automatic int sv_process_data(longint val_in, output bit [7:0] result_arr[2]);
    automatic int temp_sum;
    temp_sum = val_in % 100; 
    result_arr[0] = temp_sum[7:0];
    result_arr[1] = (temp_sum >> 8)[7:0];
    return temp_sum; 
  endfunction
  string version_str;
  bit [3:0] packed_array_arg [2]; 
  longint long_array_arg[3];
  always_comb begin
    version_str = c_get_version_string();
    out_ret_val_o = c_add_int_real(in_arg_a_i, in_arg_b_i);
    packed_array_arg[0] = 4'b1100;
    packed_array_arg[1] = 4'b0011;
    out_ret_val_o += c_context_func(packed_array_arg); 
    c_log_message("DPI function called from SystemVerilog");
    long_array_arg[0] = 100000000000000000;
    long_array_arg[1] = 200000000000000000;
    long_array_arg[2] = 300000000000000000;
    out_ret_val_o += c_process_longint_array(long_array_arg);
  end
endmodule
