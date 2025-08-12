package MyPackage;
  typedef enum logic [1:0] {
    IDLE = 2'b00,
    STATE_A = 2'b01,
    STATE_B = 2'b10,
    STATE_C = 2'b11
  } FsmState;
  typedef struct packed {
    logic [7:0] field1;
    logic [7:0] field2;
  } MyStruct_t;
  typedef union packed {
    logic [15:0] u_word;
    struct packed {
      logic [7:0] u_byte0;
      logic [7:0] u_byte1;
    } u_bytes;
  } MyUnion_t;
  class BaseClass;
    protected int base_id;
    function new(int id);
      this.base_id = id;
    endfunction
    virtual function int get_id();
      return base_id;
    endfunction
  endclass
  class DerivedClass extends BaseClass;
    int derived_val;
    function new(int id, int val);
      super.new(id);
      this.derived_val = val;
    endfunction
    function int get_id();
      return super.get_id() + derived_val;
    endfunction
  endclass
endpackage
import MyPackage::*;
interface AxiStreamIf (input logic clk, input logic rst_n);
  logic       tvalid;
  logic [31:0] tdata;
  logic       tready;
  modport Producer (
    output tvalid,
    output tdata,
    input  tready
  );
  modport Consumer (
    input  tvalid,
    input  tdata,
    output tready
  );
endinterface
module SimpleCombinational (
  input  logic [7:0] in_a,
  input  logic [7:0] in_b,
  output logic [8:0] sum_out,
  output logic        carry_out,
  output logic [31:0] class_data_out
);
  assign {carry_out, sum_out} = in_a + in_b;
  always_comb begin
    MyPackage::BaseClass base_obj;
    MyPackage::DerivedClass derived_obj;
    base_obj = new(10);
    derived_obj = new(20, 5);
    class_data_out = base_obj.get_id() + derived_obj.get_id();
  end
endmodule
module BasicSequential (
  input  logic        clk,
  input  logic        rst_n,
  input  logic [15:0] data_in,
  output logic [15:0] data_out_q
);
  logic [15:0] internal_reg;
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      internal_reg <= 16'h0000;
    end else begin
      internal_reg <= data_in;
    end
  end
  assign data_out_q = internal_reg;
  always_ff @(posedge clk) begin
    MyPackage::BaseClass seq_base_obj;
    if (data_in[0]) begin
      seq_base_obj = new(data_in[15:8]);
      void'(seq_base_obj.get_id());
    end
  end
endmodule
module MemoryModule (
  input  logic        clk,
  input  logic        rst_n,
  input  logic [3:0]  addr_in,
  input  logic        write_en,
  input  logic [7:0]  data_write_in,
  output logic [7:0]  data_read_out,
  output MyPackage::MyStruct_t struct_output
);
  logic [7:0] ram_array [0:15];
  MyPackage::MyStruct_t struct_reg;
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      for (integer i=0; i<16; i=i+1) begin
        ram_array[i] <= 8'hAA;
      end
    end else if (write_en) begin
      ram_array[addr_in] <= data_write_in;
    end
  end
  assign data_read_out = ram_array[addr_in];
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      struct_reg = '{field1: 8'h00, field2: 8'h00};
    end else begin
      struct_reg.field1 <= data_write_in;
      struct_reg.field2 <= data_write_in + 1;
    end
  end
  assign struct_output = struct_reg;
endmodule
module AxiStreamProcessor (
  input  logic          clk,
  input  logic          rst_n,
  input  logic          s_axis_tvalid,
  input  logic [31:0]   s_axis_tdata,
  output logic          s_axis_tready,
  output logic          m_axis_tvalid,
  output logic [31:0]   m_axis_tdata,
  input  logic          m_axis_tready,
  input  logic [7:0]    process_val,
  output logic [7:0]    processed_data
);
  logic [31:0] internal_data_q;
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      s_axis_tready <= 1'b0;
      internal_data_q <= 32'h0;
    end else begin
      s_axis_tready <= 1'b1;
      if (s_axis_tvalid) begin
        internal_data_q <= s_axis_tdata + process_val;
      end
    end
  end
  assign processed_data = internal_data_q[7:0];
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      m_axis_tvalid <= 1'b0;
      m_axis_tdata  <= 32'h0;
    end else if (m_axis_tready) begin
      m_axis_tvalid <= 1'b1;
      m_axis_tdata  <= internal_data_q;
    end
  end
endmodule
module ComplexClassModule (
  input  logic          clk,
  input  logic          rst_n,
  input  logic [31:0]   in_val,
  input  logic          select_base,
  output logic [31:0]   out_val_sum
);
  MyPackage::BaseClass   base_obj_local;
  MyPackage::DerivedClass derived_obj_local;
  MyPackage::BaseClass   poly_obj;
  logic [31:0] temp_sum;
  always_ff @(posedge clk or negedge rst_n) begin
    MyPackage::DerivedClass temp_derived;
    if (!rst_n) begin
      base_obj_local    = null;
      derived_obj_local = null;
      poly_obj          = null;
      temp_sum          = 32'h0;
    end else begin
      if (select_base) begin
        base_obj_local = new(in_val[7:0]);
        poly_obj       = base_obj_local;
      end else begin
        derived_obj_local = new(in_val[15:8], in_val[7:0]);
        poly_obj          = derived_obj_local;
      end
      if (poly_obj != null) begin
        temp_sum = poly_obj.get_id();
        if ($cast(temp_derived, poly_obj)) begin
          temp_sum = temp_sum + temp_derived.derived_val;
        end
      end else begin
        temp_sum = 32'hDEADBEEF;
      end
    end
  end
  assign out_val_sum = temp_sum;
endmodule
module ParameterizedLogic #(
  parameter int WIDTH = 8,
  parameter int ADD_CONST = 5
) (
  input  logic [WIDTH-1:0] data_in,
  output logic [WIDTH-1:0] data_out,
  output logic             overflow
);
  logic [WIDTH:0] temp_sum_wide;
  logic [WIDTH-1:0] non_saturated_result;
  logic [WIDTH-1:0] saturated_val;
  assign temp_sum_wide = data_in + ADD_CONST;
  assign non_saturated_result = temp_sum_wide[WIDTH-1:0];
  assign overflow = temp_sum_wide[WIDTH];
  function automatic logic [WIDTH-1:0] add_and_saturate (logic [WIDTH-1:0] a, logic [WIDTH-1:0] b);
    logic [WIDTH:0] res;
    res = a + b;
    if (res[WIDTH]) return {(WIDTH){1'b1}};
    else return res[WIDTH-1:0];
  endfunction
  assign saturated_val = add_and_saturate(data_in, {{(WIDTH-1){1'b0}}, 1'b1});
  assign data_out = non_saturated_result ^ saturated_val;
endmodule
module DataContainerModule (
  input  logic            clk,
  input  logic            rst_n,
  input  FsmState         state_sel_in,
  input  MyPackage::MyUnion_t union_data_in,
  input  logic [7:0]      input_byte_for_struct,
  output logic [1:0]      enum_val_out,
  output logic [15:0]     union_word_out,
  output MyPackage::MyStruct_t struct_data_out
);
  FsmState current_state;
  MyPackage::MyStruct_t internal_struct;
  MyPackage::MyUnion_t internal_union;
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      current_state <= IDLE;
    end else begin
      case (state_sel_in)
        IDLE:    current_state <= STATE_A;
        STATE_A: current_state <= STATE_B;
        STATE_B: current_state <= STATE_C;
        STATE_C: current_state <= IDLE;
      endcase
    end
  end
  assign enum_val_out = current_state;
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      internal_struct = '{field1: 8'h00, field2: 8'h00};
    end else begin
      internal_struct.field1 <= input_byte_for_struct;
      internal_struct.field2 <= input_byte_for_struct + current_state;
    end
  end
  assign struct_data_out = internal_struct;
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      internal_union.u_word <= 16'h0000;
    end else begin
      internal_union <= union_data_in;
    end
  end
  assign union_word_out = internal_union.u_word;
endmodule
module FunctionTaskModule (
  input  logic [7:0] in_val1,
  input  logic [7:0] in_val2,
  input  logic       enable_task,
  output logic [8:0] sum_func_out,
  output logic [7:0] task_result_out
);
  logic [7:0] task_internal_var;
  function automatic logic [8:0] calculate_sum (input logic [7:0] a, input logic [7:0] b);
    return a + b;
  endfunction
  assign sum_func_out = calculate_sum(in_val1, in_val2);
  task automatic my_processing_task (input logic [7:0] data_in, output logic [7:0] processed_data);
    processed_data = data_in * 2;
    if (processed_data > 8'hFF) begin
      processed_data = 8'hFF;
    end
  endtask
  always_comb begin
    if (enable_task) begin
      my_processing_task(in_val1, task_internal_var);
    end else begin
      task_internal_var = 8'h00;
    end
  end
  assign task_result_out = task_internal_var;
endmodule
