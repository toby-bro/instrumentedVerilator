interface my_interface (input bit clk);
  logic [3:0] data;
  modport master (output data);
  modport slave (input data);
endinterface
class BaseClass;
  local int base_data;
  const int FIXED_VAL = 100;
  function new(int d);
    this.base_data = d;
  endfunction
  virtual function void print_data();
  endfunction
endclass
class DerivedClass extends BaseClass;
  int derived_data;
  function new(int d_base, int d_derived);
    super.new(d_base);
    this.derived_data = d_derived;
  endfunction
  virtual function void print_data();
  endfunction
endclass
class DummyClass;
  int dummy_val;
  function new(int v);
    this.dummy_val = v;
  endfunction
endclass
module BasicVerilogAndOps (
  input  wire [7:0] in_data_A,
  input  wire [7:0] in_data_B,
  input  wire        in_sel,
  output reg  [7:0] out_result_C
);
  wire [7:0] temp_wire_X;
  reg  [7:0] temp_reg_Y;
  assign temp_wire_X = in_data_A + in_data_B; 
  assign temp_reg_Y  = in_data_A - in_data_B; 
  assign temp_reg_Y  = in_data_A * in_data_B; 
  assign temp_reg_Y  = in_data_A / in_data_B; 
  assign temp_reg_Y  = in_data_A % in_data_B; 
  always @(*) begin 
    reg  [7:0] local_reg_Val; 
    wire [7:0] local_wire_Val; 
    logic [7:0] local_logic_Val; 
    local_reg_Val = in_data_A & in_data_B; 
    local_reg_Val = in_data_A | in_data_B; 
    local_reg_Val = in_data_A ^ in_data_B; 
    local_reg_Val = ~in_data_A;            
    local_reg_Val = !in_sel;               
    local_reg_Val = (in_data_A == in_data_B) ? 8'hAA : 8'h55; 
    local_reg_Val = (in_data_A != in_data_B) ? 8'hAA : 8'h55; 
    local_reg_Val = (in_data_A === in_data_B) ? 8'hAA : 8'h55; 
    local_reg_Val = (in_data_A !== in_data_B) ? 8'hAA : 8'h55; 
    local_reg_Val = (in_data_A < in_data_B) ? 8'hAA : 8'h55; 
    local_reg_Val = (in_data_A > in_data_B) ? 8'hAA : 8'h55; 
    local_reg_Val = (in_data_A <= in_data_B) ? 8'hAA : 8'h55; 
    local_reg_Val = (in_data_A >= in_data_B) ? 8'hAA : 8'h55; 
    local_reg_Val = &(in_data_A);  
    local_reg_Val = |(in_data_A);  
    local_reg_Val = ^(in_data_A);  
    local_reg_Val = {in_data_A[3:0], in_data_B[3:0]};
    local_reg_Val = {2{in_data_A[3:0]}};
    local_reg_Val = in_data_A << 2;  
    local_reg_Val = in_data_A >> 2;  
    local_reg_Val = in_data_A <<< 2; 
    local_reg_Val = in_data_A >>> 2; 
    local_reg_Val = in_data_A ^~ in_data_B; 
    local_reg_Val = in_data_A ~^ in_data_B; 
    local_reg_Val = (in_sel) ? in_data_A : in_data_B; 
    if (in_sel) begin
      local_reg_Val = temp_wire_X;
    end else begin
      local_reg_Val = temp_reg_Y;
    end
    local_wire_Val = 10;            
    local_logic_Val = 8'hF0;        
    local_reg_Val = 4'b1010;        
    local_reg_Val = 12'o777;        
    local_logic_Val = 0.1234;       
    local_logic_Val = 1.23E-4;      
  end
  out_result_C = temp_reg_Y; 
endmodule
module SV2005Features (
  input  bit clk_B,
  input  bit reset_B,
  input  signed [15:0] in_signed_data_B,
  input  [1:0]         in_case_sel_B,
  output unsigned [15:0] out_unsigned_val_B
);
  localparam int MAX_DEPTH = 5; 
  genvar j; 
  typedef enum logic [1:0] { 
    STATE_INIT = 2'b00,
    STATE_WORK = 2'b01,
    STATE_DONE = 2'b10
  } my_state_e;
  my_state_e current_fsm_state;
  typedef struct packed { 
    bit [7:0] id;
    int value;
  } my_packet_s;
  typedef union packed { 
    my_packet_s packet_part;
    longint full_data; 
  } my_union_u;
  bit [3:0] my_bit_var; 
  byte my_byte_var; 
  shortint my_shortint_var; 
  shortreal my_shortreal_var; 
  string my_string_var; 
  initial begin 
    DummyClass dummy_obj;
    dummy_obj = new(MAX_DEPTH); 
  end
  generate 
    for (j = 0; j < 1; j = j + 1) begin : gen_loop 
      logic [15:0] signed_temp;
      assign signed_temp = in_signed_data_B; 
      assign out_unsigned_val_B = $unsigned(signed_temp); 
      assign out_unsigned_val_B = $signed(out_unsigned_val_B); 
    end
  endgenerate 
  always @(in_case_sel_B or in_signed_data_B) begin
    case (in_case_sel_B) 
      2'b00: begin 
        out_unsigned_val_B = 16'h0000;
        my_bit_var = 4'b0101;
      end
      2'b01: begin
        out_unsigned_val_B = in_signed_data_B + current_fsm_state;
        my_byte_var = 8'hAA;
      end
      default: begin 
        out_unsigned_val_B = 16'hFFFF;
        my_shortint_var = 16'hBBBB;
      end
    endcase 
    casex (in_case_sel_B) 
      2'b0X: out_unsigned_val_B = 16'h1111;
      default: out_unsigned_val_B = 16'h2222;
    endcasex 
    casez (in_case_sel_B) 
      2'b1Z: out_unsigned_val_B = 16'h3333;
      default: out_unsigned_val_B = 16'h4444;
    endcasez 
    my_shortreal_var = 0.5s;
    my_string_var = "Hello SystemVerilog Types";
  end
endmodule
module AdvancedSVFeatures (
  input  bit clk_C,
  input  bit rst_C,
  input  logic [7:0] data_in_C,
  output logic [7:0] data_out_C
);
  real pi_val = 3.14159; 
  alias data_out_C = data_in_C; 
  class PureVirtualBase;
    pure virtual function int get_value(); 
  endclass
  class WithProtected;
    protected int secret_data; 
  endclass
  always_ff @(posedge clk_C or posedge rst_C) begin
    longint time_stamp;
    real    calc_res;
    int     rand_val;
    void    void_ret; 
    chandle c_ptr_val = null; 
    if (rst_C) begin
      data_out_C <= 8'h00;
    end else begin
      data_out_C <= data_in_C;
      calc_res = $acos(0.5);      
      calc_res = $acosh(1.1);
      calc_res = $asin(0.2);
      calc_res = $asinh(0.2);
      calc_res = $atan(1.0);
      calc_res = $atan2(1.0, 1.0);
      calc_res = $atanh(0.1);
      calc_res = $cos(pi_val);
      calc_res = $cosh(0.1);
      calc_res = $exp(1.0);
      calc_res = $ln(2.0);
      calc_res = $log10(100.0);
      calc_res = $sin(pi_val/2);
      calc_res = $sinh(0.1);
      calc_res = $tan(pi_val/4);
      calc_res = $tanh(0.1);
      calc_res = $ceil(3.14);
      calc_res = $floor(3.14);
      calc_res = $hypot(3.0, 4.0);
      calc_res = $pow(2.0, 3.0);
      calc_res = $sqrt(25.0);
      rand_val = $itor(data_in_C); 
      calc_res = $rtoi(calc_res);
      rand_val = $bitstoreal(32'h00000000);
      rand_val = $realtobits(calc_res);
      rand_val = $bitstoshortreal(16'h0000);
      rand_val = $shortrealtobits(0.0s);
      void_ret = $cast(int'(data_in_C));
      time_stamp = $time;     
      time_stamp = $realtime; 
      time_stamp = $stime;    
    end
  end
  (* my_attr = "value" *) logic [3:0] attributed_logic_A; 
  logic (*other_attr*) [3:0] attributed_logic_B; 
  function void dummy_sv_keywords_lexer_hits();
    int local_dummy_int;
    local_dummy_int = 1; 
  endfunction
endmodule
module VerilatorAndPreprocessor (
  input  bit clk_D,
  input  bit enable_D,
  output logic [7:0] out_val_D
);
  `timescale 1ns / 1ps 
  `celldefine 
  `default_nettype wire 
  `undefineall 
  `define MY_DEFINE_A 
  `ifdef MY_DEFINE_A 
    localparam int COND_VAL = 1;
  `else 
    localparam int COND_VAL = 0;
  `endif 
  `undef MY_DEFINE_A 
  `include "dummy_file.vh" 
  `pragma some_tool_pragma "value" 
  `protect 
  `endprotect 
  `unconnected_drive pull0 
  `unconnected_drive pull1 
  `resetall 
  `begin_keywords "1800-1995" 
  `end_keywords 
  `begin_keywords "1800-2001-conf" 
  `end_keywords
  `begin_keywords "1800-2001-nc" 
  `end_keywords
  `begin_keywords "1800-2005" 
  `end_keywords
  `begin_keywords "1800-2009" 
  `end_keywords
  `begin_keywords "1800-2012" 
  `end_keywords
  `begin_keywords "1800-2017" 
  `end_keywords
  `begin_keywords "1800-2023" 
  `end_keywords
  `begin_keywords "AMS" 
  `end_keywords
  `begin_keywords "latest" 
  `end_keywords
  `line 1 "some_file.sv" 
  `FILE 
  `__FILE__ 
  `LINE 
  `__LINE__ 
  `__FUNC__ 
  `begin_protected 
  `end_protected 
  `elseifdef 
  `end_compilation_unit 
  `nounconnected_drive 
  `protected 
  `undefineall 
  always @(enable_D) begin
    out_val_D = enable_D ? 8'hFF : 8'h00; 
  end
endmodule
