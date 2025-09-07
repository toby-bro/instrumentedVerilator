package my_data_pkg;
  typedef struct packed {
    logic [7:0] val_a;
    int         val_b;
  } my_packed_struct_t;
  typedef enum {
    STATE_IDLE,
    STATE_BUSY,
    STATE_DONE
  } fsm_state_t;
  class MyVerilogClass;
    int class_input_val;
    output int class_output_val;
    public int my_class_public_var = 100;
    function new(int init_val);
      this.class_input_val = init_val;
      this.class_output_val = 0;
    endfunction
    function void process_data(int data_in, output int data_out);
      class_input_val += data_in;
      class_output_val = class_input_val * 2;
      data_out = class_output_val;
      my_class_public_var = class_input_val / 2;
    endfunction
    virtual function string get_info();
      return $sformatf("Class instance with input_val: %0d", class_input_val);
    endfunction
  endclass
  event global_event_trigger;
endpackage
module ModA #(
  parameter int WIDTH_A = 8,
  parameter string MSG_A = "HelloModA"
) (
  input logic           clk,
  input logic           rst_n,
  input logic [WIDTH_A-1:0] data_in_a,
  output logic [WIDTH_A-1:0] data_out_a
);
  import my_data_pkg::*;
  localparam int DEPTH_A = 4;
  logic [WIDTH_A-1:0] internal_reg_a;
  int                counter_a;
  real               real_val_a = 3.14;
  string             current_msg_a = MSG_A;
  fsm_state_t        current_state_a = STATE_IDLE;
  var logic [WIDTH_A-1:0] public_var_a;
  logic [7:0] packed_array_a [DEPTH_A];
  my_packed_struct_t struct_array_a [2];
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      internal_reg_a <= '0;
      counter_a <= 0;
      public_var_a <= '0;
      current_state_a <= STATE_IDLE;
      for (int i=0; i<DEPTH_A; i++) packed_array_a[i] <= '0;
      struct_array_a[0] <= '{val_a:8'd0, val_b:0};
      struct_array_a[1] <= '{val_a:8'd0, val_b:0};
    end else begin
      internal_reg_a <= data_in_a + 1;
      counter_a <= counter_a + 1;
      public_var_a <= data_in_a;
      packed_array_a[0] <= data_in_a[7:0];
      struct_array_a[0].val_a <= data_in_a[7:0];
      struct_array_a[1].val_b <= counter_a;
      case (current_state_a)
        STATE_IDLE: begin
          if (counter_a > 5) current_state_a <= STATE_BUSY;
        end
        STATE_BUSY: begin
          if (counter_a > 10) current_state_a <= STATE_DONE;
        end
        STATE_DONE: begin
          current_state_a <= STATE_IDLE;
        end
      endcase
    end
  end
  assign data_out_a = internal_reg_a;
endmodule
module ModB (
  input int in_b,
  input int idx_b,
  output int out_b
);
  localparam int NUM_INSTANCES = 2;
  int multi_dim_array [2][3];
  const int FIXED_VALUE = 42;
  genvar i;
  for (i = 0; i < NUM_INSTANCES; i++) begin : gen_block_inst
    ModC #(
      .ID_C(i)
    ) mod_c_inst (
      .dpi_in(in_b + i),
      .cover_input(idx_b),
      .dpi_out(out_b_internal[i])
    );
  end
  int out_b_internal[NUM_INSTANCES];
  assign out_b = out_b_internal[0] + out_b_internal[1];
  always_comb begin
    for (int j=0; j<2; j++) begin
      for (int k=0; k<3; k++) begin
        multi_dim_array[j][k] = j * k + FIXED_VALUE;
      end
    end
  end
endmodule
module ModC #(
  parameter int ID_C = 0
) (
  input int dpi_in,
  input logic [3:0] cover_input,
  output int dpi_out
);
  import "DPI-C" function int c_import_add(int a, int b);
  import "DPI-C" function void c_import_log_string(string msg);
  import "DPI-C" function real c_import_multiply_real(real val1, real val2);
  import "DPI-C" function void c_import_array_op(input int in_arr[], output int out_val);
  export "DPI-C" function verilog_export_subtract;
  function int verilog_export_subtract(int x, int y);
    return x - y;
  endfunction
  covergroup my_covergroup @(posedge cover_input[0]);
    coverpoint cover_input {
      bins zero = {0};
      bins one_to_three = {1, 2, 3};
      bins others = default;
    }
    my_cross: cross cover_input, ID_C_cp;
  endgroup
  coverpoint_param_t ID_C_cp = new(ID_C);
  class coverpoint_param_t;
    int param_val;
    function new(int p);
      param_val = p;
    endfunction
    function int get(); return param_val; endfunction
  endclass
  my_covergroup cov_inst = new();
  int temp_result;
  real temp_real_result;
  always_comb begin
    temp_result = c_import_add(dpi_in, ID_C);
    temp_real_result = c_import_multiply_real(dpi_in * 1.0, ID_C * 2.0);
    int my_array[3] = {10, 20, 30};
    int array_out_val;
    c_import_array_op(my_array, array_out_val);
    dpi_out = temp_result + array_out_val;
  end
endmodule
module ModD (
  input logic clk,
  input logic rst_n,
  input int   class_input_data,
  input logic event_trigger_in,
  output int  class_output_data
);
  import my_data_pkg::*;
  MyVerilogClass my_obj;
  int internal_class_output;
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      if (my_obj != null) begin
        my_obj.process_data(0, internal_class_output);
        $cast(my_obj, null);
      end
      my_obj = new(class_input_data);
    end else begin
      if (my_obj == null) begin
        my_obj = new(class_input_data);
      end else begin
        my_obj.process_data(class_input_data, internal_class_output);
        if (event_trigger_in) begin
          -> global_event_trigger;
        end
      end
    end
  end
  assign class_output_data = internal_class_output;
endmodule
