package my_pkg;
  typedef struct packed {
    logic [7:0] data;
    logic       valid;
  } packed_s_t;
  typedef struct {
    int   addr;
    logic [15:0] value;
  } unpacked_s_t;
  class MyClass;
    int class_member_int;
    real class_member_real;
    string class_member_string;
    logic [31:0] class_member_wide;
    unpacked_s_t class_member_struct;
    int assoc_array_mem[*];
    int dyn_array_mem[];
    int queue_mem[$];
    logic [7:0] _internal_logic;
    rand int rand_val;
    process my_process_handle;
    function new();
      class_member_int = 10;
      class_member_real = 3.14;
      class_member_string = "Hello from class";
      class_member_wide = 32'hFEED_BEEF;
      class_member_struct.addr = 1;
      class_member_struct.value = 16'hAAAA;
      assoc_array_mem[0] = 100;
      assoc_array_mem[1] = 200;
      dyn_array_mem = new[2];
      dyn_array_mem[0] = 5;
      dyn_array_mem[1] = 6;
      queue_mem.push_back(10);
      queue_mem.push_back(20);
      _internal_logic = 8'hDE;
      my_process_handle = process::self();
      void'(this.randomize());
    endfunction : new
    function int get_class_member_int();
      return class_member_int;
    endfunction : get_class_member_int
    function void set_class_member_int(input int val);
      class_member_int = val;
    endfunction : set_class_member_int
    function int get_local_var(input int i_val);
      int local_var_in_func = i_val * 2;
      return local_var_in_func;
    endfunction
  endclass : MyClass
endpackage : my_pkg
module LogicOps (
  input  logic [3:0] in_val,
  output logic [3:0] out_val
);
  assign out_val = in_val;
endmodule
module ClassInstantiationModule (
  input bit create_instance,
  input int input_for_method,
  output int instance_val,
  output int local_var_from_method
);
  import my_pkg::MyClass;
  MyClass my_instance;
  always_comb begin
    if (create_instance) begin
      my_instance = new();
      instance_val = my_instance.get_class_member_int();
      my_instance.set_class_member_int(input_for_method);
      local_var_from_method = my_instance.get_local_var(input_for_method + 5);
    end else begin
      instance_val = 0;
      local_var_from_method = 0;
    end
  end
endmodule : ClassInstantiationModule
module OperatorCoverage (
  input  logic [7:0] in_a,
  input  logic [7:0] in_b,
  input  logic [31:0] in_wide_a,
  input  logic [31:0] in_wide_b,
  input  bit         in_sel,
  output logic [7:0] out_add,
  output logic [7:0] out_sub,
  output logic [7:0] out_and,
  output logic [7:0] out_or,
  output logic [7:0] out_xor,
  output logic [7:0] out_not,
  output logic [7:0] out_shl,
  output logic [7:0] out_shr,
  output logic [31:0] out_wide_mul,
  output logic [31:0] out_wide_div,
  output logic [7:0] out_ternary,
  output logic [15:0] out_concat_a,
  output logic [15:0] out_concat_b,
  output logic [1:0] out_part_select,
  output logic [31:0] out_bit_rep,
  output logic [31:0] out_vec_rep,
  output logic        out_eq,
  output logic        out_ne,
  output logic        out_lt,
  output logic        out_ge,
  output logic [7:0]  out_red_and,
  output logic [7:0]  out_red_or,
  output logic [7:0]  out_red_xor
);
  assign out_add = in_a + in_b;
  assign out_sub = in_a - in_b;
  assign out_and = in_a & in_b;
  assign out_or  = in_a | in_b;
  assign out_xor = in_a ^ in_b;
  assign out_not = ~in_a;
  assign out_shl = in_a << 2;
  assign out_shr = in_b >> 1;
  assign out_wide_mul = in_wide_a * in_wide_b;
  assign out_wide_div = in_wide_a / in_wide_b;
  assign out_ternary = in_sel ? in_a : in_b;
  assign out_concat_a = {in_a, in_b};
  assign out_concat_b = {4'b0, in_b, 4'b1};
  assign out_part_select = in_wide_a[1:0];
  assign out_bit_rep = {32{in_sel}};
  assign out_vec_rep = {2{in_a, in_b}};
  assign out_eq = (in_a == in_b);
  assign out_ne = (in_wide_a != in_wide_b);
  assign out_lt = (in_a < in_b);
  assign out_ge = (in_wide_a >= in_wide_b);
  assign out_red_and = &in_a;
  assign out_red_or  = |in_b;
  assign out_red_xor = ^in_a;
endmodule : OperatorCoverage
module SformatfCoverage (
    input logic [7:0] data_in,
    input int         value_in,
    output string     sformatf_out_string,
    output logic [31:0] sformat_packed_out
);
    string sformat_var;
    always_comb begin
        sformatf_out_string = $sformatf("Data: %h, Value: %d", data_in, value_in);
        $sformat(sformat_var, "Packed data is %h. Value is %d", data_in, value_in);
        sformat_packed_out = sformat_var.len();
        sformatf_out_string = $sformatf("Real: %f, Time: %t", 3.14159, $time);
    end
endmodule : SformatfCoverage
module DisplayAndScanCoverage (
  input  logic [7:0]  byte_in,
  input  logic [31:0] int_in,
  input  real         real_in,
  input  string       string_in,
  input  my_pkg::packed_s_t packed_struct_in,
  output logic [7:0]  byte_out
);
  logic [7:0] scan_byte;
  int         scan_int;
  real        scan_real;
  string      scan_string;
  logic [7:0] unpacked_arr[4] = '{8'h11, 8'h22, 8'h33, 8'h44};
  always_comb begin
    automatic string sscanf_source_str = "42 3.14159 test_string";
    automatic int    sscanf_val_int;
    automatic real   sscanf_val_real;
    automatic string sscanf_val_string;
    $display("Test: Byte=%h, Int=%d, Real=%f", byte_in, int_in, real_in);
    $display("Octal=%o, Binary=%b, Char=%c", byte_in, byte_in, byte_in);
    $display("Hex Upper=%X", int_in);
    $display("Pointer format for packed struct = %p", packed_struct_in);
    $display("Time=%t, E-format=%e, G-format=%g", $time, real_in, real_in);
    $display("String='%s'", string_in);
    $display("Signed Decimal = %d", int_in);
    $display("Unsigned Decimal = %0d", byte_in);
    $display("Value (v) = %v, Uninitialized (u) = %u, Zeros (z) = %z", byte_in, byte_in, byte_in);
    void'($sscanf(sscanf_source_str, "%d %f %s", sscanf_val_int, sscanf_val_real, sscanf_val_string));
    byte_out = byte_in;
  end
endmodule : DisplayAndScanCoverage
