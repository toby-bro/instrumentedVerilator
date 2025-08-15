package my_data_types_pkg;
  typedef enum logic [1:0] {
    IDLE = 2'b00,
    BUSY = 2'b01,
    DONE = 2'b10
  } State_e;
  typedef enum logic [2:0] {
    ADD = 3'b001,
    SUB = 3'b010,
    MUL = 3'b011
  } Operation_e;
  typedef enum logic [64:0] {
    LARGE_A = 65'd1,
    LARGE_B = 65'd2
  } LargeEnum_e;
  typedef struct {
    logic [7:0] field_a;
    logic [7:0] field_b;
    State_e     current_state;
    int         array_of_ints[3];
  } MyUnpackedStruct_t;
  typedef union {
    logic [7:0] u_field_x;
    logic [15:0] u_field_y;
    int          u_field_z;
  } MyUnpackedUnion_t;
  typedef struct packed {
    logic [3:0] sub_field_a;
    logic [7:0] sub_field_b;
    logic [3:0] sub_field_c;
  } MyNestedPackedStruct_t;
  typedef struct packed {
    logic [1:0] p_field1;
    logic [1:0] p_field2;
    logic [11:0] p_field3;
    MyNestedPackedStruct_t nested_packed;
    logic [7:0] array_packed[2];
  } MyPackedStruct_t;
  typedef union packed {
    logic [7:0] pu_field_x;
    logic [15:0] pu_field_y;
  } MyPackedUnion_t;
  typedef struct packed {
    logic [1:0] p_field1;
    logic [1:0] p_field2;
    logic [11:0] p_field3;
    MyNestedPackedStruct_t nested_packed;
    logic [7:0] array_packed[2];
  } MyPackedStructForRand_t;
endpackage
import my_data_types_pkg::*;
module DataTypesModule #(
  parameter int WIDTH_P = 8,
  parameter int DEPTH_L = 4
) (
  input logic [WIDTH_P-1:0] in_data_lp,
  input bit in_enable_b,
  input int in_count_i,
  input byte in_byte_b,
  input shortint in_short_s,
  input longint in_long_l,
  input real in_real_r,
  output logic [WIDTH_P-1:0] out_result_lp,
  output bit out_status_b,
  output int out_sum_i,
  output byte out_byte_plus_b
);
  logic [WIDTH_P-1:0] internal_reg_lp;
  bit [DEPTH_L-1:0] internal_bit_array_ba;
  int internal_int_array_ia [];
  real internal_real_val_r;
  string internal_string_val_s = "hello";
  logic [255:0] wide_signal_l;
  initial begin
    internal_int_array_ia = new[DEPTH_L];
  end
  function int calculate_sum(int a, int b);
    return a + b;
  endfunction
  function automatic int multiply_values(int val1, int val2);
    return val1 * val2;
  endfunction
  always_comb begin
    internal_reg_lp = in_data_lp;
    internal_real_val_r = in_real_r;
    wide_signal_l = {248'b0, in_data_lp};
  end
  always_comb begin
    out_result_lp = internal_reg_lp;
    out_status_b = in_enable_b;
    out_sum_i = calculate_sum(in_count_i, DEPTH_L);
    out_byte_plus_b = in_byte_b + 1;
    for (int i = 0; i < DEPTH_L; i++) begin
      internal_bit_array_ba[i] = in_enable_b;
      internal_int_array_ia[i] = multiply_values(in_count_i, i);
    end
  end
endmodule
module EnumStructUnionModule (
  input logic [1:0] in_state_val,
  input logic [2:0] in_op_type_val,
  input logic [7:0] in_struct_mem_a,
  input logic [7:0] in_union_mem_c,
  output logic [7:0] out_struct_mem_b,
  output logic [7:0] out_union_data
);
  MyUnpackedStruct_t my_unpacked_struct_var;
  MyUnpackedUnion_t my_unpacked_union_var;
  State_e current_module_state;
  Operation_e current_operation;
  LargeEnum_e large_enum_var;
  always_comb begin
    current_module_state = State_e'(in_state_val);
    current_operation = Operation_e'(in_op_type_val);
    large_enum_var = LARGE_A;
    my_unpacked_struct_var.field_a = in_struct_mem_a;
    my_unpacked_struct_var.current_state = current_module_state;
    my_unpacked_struct_var.array_of_ints[0] = 10;
    my_unpacked_struct_var.array_of_ints[1] = 20;
    my_unpacked_struct_var.array_of_ints[2] = 30;
    my_unpacked_struct_var.field_b = 8'd5;
    my_unpacked_union_var.u_field_x = in_union_mem_c;
    out_struct_mem_b = my_unpacked_struct_var.field_b;
    out_union_data = my_unpacked_union_var.u_field_x;
  end
endmodule
module PackedTypesLogicModule (
  input MyPackedStruct_t in_packed_struct,
  input MyPackedUnion_t in_packed_union,
  output logic [15:0] out_packed_s_data,
  output logic [7:0] out_packed_u_data
);
  MyPackedStruct_t internal_packed_struct;
  MyPackedUnion_t internal_packed_union;
  MyNestedPackedStruct_t nested_temp;
  always_comb begin
    internal_packed_struct = in_packed_struct;
    internal_packed_union = in_packed_union;
    out_packed_s_data = {internal_packed_struct.p_field1, internal_packed_struct.p_field2, internal_packed_struct.p_field3};
    out_packed_u_data = internal_packed_union.pu_field_x;
    nested_temp = internal_packed_struct.nested_packed;
    nested_temp.sub_field_a = in_packed_struct.nested_packed.sub_field_a;
    internal_packed_struct.nested_packed.sub_field_b = internal_packed_struct.array_packed[0];
  end
endmodule
module ClassAndRandModule (
  input bit in_rand_trigger,
  input logic [7:0] in_a,
  input logic [7:0] in_b,
  output logic [7:0] out_sum,
  output logic [7:0] out_product,
  output logic [7:0] out_rand_val_a,
  output logic [7:0] out_rand_val_b
);
  class BaseClass;
    rand int r_base_val;
    logic base_internal;
    function new();
      r_base_val = 0;
      base_internal = 0;
    endfunction
    function int get_base_val();
      return r_base_val;
    endfunction
    constraint base_constraint {
      r_base_val inside {[0:100]};
    }
  endclass
  class DerivedClass extends BaseClass;
    rand int r_derived_val;
    rand MyPackedStructForRand_t rand_packed_struct;
    int m_val;
    function new(int init_val);
      super.new();
      r_derived_val = 0;
      m_val = init_val;
    endfunction
    task increment_val(int delta);
      m_val += delta;
    endtask
    constraint derived_constraint {
      r_derived_val inside {[10:50]};
      r_base_val == r_derived_val * 2;
      solve r_derived_val before r_base_val;
      rand_packed_struct.p_field1 != rand_packed_struct.p_field2;
      foreach(rand_packed_struct.array_packed[i]) {
        rand_packed_struct.array_packed[i] < 128;
      }
    }
  endclass
  DerivedClass my_obj_instance;
  always_ff @(posedge in_rand_trigger) begin
    if (my_obj_instance == null) begin
      my_obj_instance = new(10);
    end
    if (my_obj_instance.randomize()) begin
      out_rand_val_a = my_obj_instance.r_base_val;
      out_rand_val_b = my_obj_instance.r_derived_val;
      out_sum = my_obj_instance.m_val + in_a;
      my_obj_instance.increment_val(in_b);
      out_product = my_obj_instance.rand_packed_struct.nested_packed.sub_field_b;
    end else begin
      out_rand_val_a = 0;
      out_rand_val_b = 0;
      out_sum = 0;
      out_product = 0;
    end
  end
endmodule
module DPIAndFunctionModule (
  input bit in_clk,
  input bit in_reset,
  input int in_value,
  output int out_processed_value
);
  import "DPI-C" function int dpi_add_one(input int val);
  export "DPI-C" function dpi_multiply_by_two;
  function int dpi_multiply_by_two(input int val);
    return val * 2;
  endfunction
  int internal_value;
  always_ff @(posedge in_clk or posedge in_reset) begin
    if (in_reset) begin
      internal_value <= 0;
      out_processed_value <= 0;
    end else begin
      internal_value <= dpi_add_one(in_value);
      out_processed_value <= dpi_multiply_by_two(internal_value);
    end
  end
endmodule
module TopLevelInstantiator (
  input logic clk,
  input logic rst_n,
  input logic [15:0] data_in_wide,
  output logic [7:0] final_out_a,
  output logic [7:0] final_out_b
);
  logic [7:0] dt_out_result;
  bit dt_out_status;
  int dt_out_sum;
  byte dt_out_byte_plus;
  logic [7:0] esu_out_struct_b;
  logic [7:0] esu_out_union_data;
  MyPackedStruct_t pt_in_struct;
  MyPackedUnion_t pt_in_union;
  logic [15:0] pt_out_packed_s_data;
  logic [7:0] pt_out_packed_u_data;
  bit cr_in_rand_trigger;
  logic [7:0] cr_in_a;
  logic [7:0] cr_in_b;
  logic [7:0] cr_out_sum;
  logic [7:0] cr_out_product;
  logic [7:0] cr_out_rand_val_a;
  logic [7:0] cr_out_rand_val_b;
  int dpi_in_value;
  int dpi_out_processed_value;
  DataTypesModule #(.WIDTH_P(8), .DEPTH_L(4)) i_data_types_module (
    .in_data_lp(data_in_wide[7:0]),
    .in_enable_b(rst_n),
    .in_count_i(10),
    .in_byte_b(data_in_wide[7:0]),
    .in_short_s(20),
    .in_long_l(30),
    .in_real_r(3.14),
    .out_result_lp(dt_out_result),
    .out_status_b(dt_out_status),
    .out_sum_i(dt_out_sum),
    .out_byte_plus_b(dt_out_byte_plus)
  );
  EnumStructUnionModule i_esu_module (
    .in_state_val(data_in_wide[1:0]),
    .in_op_type_val(data_in_wide[2:0]),
    .in_struct_mem_a(data_in_wide[7:0]),
    .in_union_mem_c(data_in_wide[7:0]),
    .out_struct_mem_b(esu_out_struct_b),
    .out_union_data(esu_out_union_data)
  );
  always_comb begin
    pt_in_struct.p_field1 = data_in_wide[1:0];
    pt_in_struct.p_field2 = data_in_wide[3:2];
    pt_in_struct.p_field3 = data_in_wide[14:4];
    pt_in_struct.nested_packed.sub_field_a = data_in_wide[3:0];
    pt_in_struct.nested_packed.sub_field_b = data_in_wide[7:0];
    pt_in_struct.nested_packed.sub_field_c = data_in_wide[3:0];
    pt_in_struct.array_packed[0] = data_in_wide[7:0];
    pt_in_struct.array_packed[1] = data_in_wide[15:8];
    pt_in_union.pu_field_x = data_in_wide[7:0];
    cr_in_rand_trigger = clk;
    cr_in_a = data_in_wide[7:0];
    cr_in_b = data_in_wide[7:0] + 1;
    dpi_in_value = data_in_wide;
  end
  PackedTypesLogicModule i_packed_types_module (
    .in_packed_struct(pt_in_struct),
    .in_packed_union(pt_in_union),
    .out_packed_s_data(pt_out_packed_s_data),
    .out_packed_u_data(pt_out_packed_u_data)
  );
  ClassAndRandModule i_class_rand_module (
    .in_rand_trigger(cr_in_rand_trigger),
    .in_a(cr_in_a),
    .in_b(cr_in_b),
    .out_sum(cr_out_sum),
    .out_product(cr_out_product),
    .out_rand_val_a(cr_out_rand_val_a),
    .out_rand_val_b(cr_out_rand_val_b)
  );
  DPIAndFunctionModule i_dpi_function_module (
    .in_clk(clk),
    .in_reset(~rst_n),
    .in_value(dpi_in_value),
    .out_processed_value(dpi_out_processed_value)
  );
  assign final_out_a = dt_out_result + esu_out_struct_b;
  assign final_out_b = pt_out_packed_u_data + cr_out_rand_val_a + dpi_out_processed_value[7:0];
endmodule
