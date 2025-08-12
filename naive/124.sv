typedef struct packed {
  logic [3:0] part_a;
  logic [3:0] part_b;
} my_struct_t;
module CombLogicStruct (
  input logic [7:0] in_data,
  input logic [1:0] sel,
  output logic [7:0] out_mux
);
  my_struct_t data_split;
  logic [7:0] temp_result;
  always_comb begin
    data_split.part_a = in_data[7:4];
    data_split.part_b = in_data[3:0];
    case (sel)
      2'b00: temp_result = {data_split.part_a, data_split.part_b};
      2'b01: temp_result = {data_split.part_b, data_split.part_a};
      2'b10: temp_result = in_data + 8'd1;
      default: temp_result = in_data - 8'd1;
    endcase
    out_mux = temp_result;
  end
endmodule
module SeqLogicEnum (
  input logic clk,
  input logic rst_n,
  input logic [1:0] next_state_ctrl,
  output logic [3:0] current_val
);
  typedef enum logic [1:0] {
    S_IDLE,
    S_ADD,
    S_SUB,
    S_RESET
  } state_e;
  state_e current_state, next_state;
  logic [3:0] counter_reg;
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      current_state <= S_IDLE;
      counter_reg <= 4'd0;
    end else begin
      current_state <= next_state;
      counter_reg <= (current_state == S_ADD) ? counter_reg + 4'd1 :
                     (current_state == S_SUB) ? counter_reg - 4'd1 :
                     (current_state == S_RESET) ? 4'd0 :
                     counter_reg;
    end
  end
  always_comb begin
    case (next_state_ctrl)
      2'b00: next_state = S_IDLE;
      2'b01: next_state = S_ADD;
      2'b10: next_state = S_SUB;
      default: next_state = S_RESET;
    endcase
  end
  assign current_val = counter_reg;
endmodule
module GenBlockParams #(
  parameter int ARRAY_SIZE = 4,
  parameter int DATA_WIDTH = 8
) (
  input logic enable_array_ops,
  input logic [DATA_WIDTH-1:0] data_in_gen,
  output logic [DATA_WIDTH*2-1:0] result_sum_gen
);
  logic [DATA_WIDTH-1:0] data_array [ARRAY_SIZE-1:0];
  logic [DATA_WIDTH*2-1:0] sum_internal;
  genvar i;
  generate
    for (i = 0; i < ARRAY_SIZE; i = i + 1) begin : gen_assign
      always_comb begin
        data_array[i] = data_in_gen + i;
      end
    end
  endgenerate
  always_comb begin
    sum_internal = 0;
    if (enable_array_ops) begin
      for (int k = 0; k < ARRAY_SIZE; k++) begin
        sum_internal = sum_internal + data_array[k];
      end
    end else begin
      sum_internal = data_in_gen * 2;
    end
    result_sum_gen = sum_internal;
  end
endmodule
class MySimpleClass;
  logic [7:0] internal_data;
  function new();
    internal_data = 8'd0;
  endfunction
  function void set_data(logic [7:0] val);
    internal_data = val;
  endfunction
  function logic [7:0] get_data();
    return internal_data;
  endfunction
endclass
module ClassUsage (
  input logic [7:0] init_val,
  input logic set_val_en,
  output logic [7:0] current_read_val
);
  MySimpleClass my_object_h;
  logic [7:0] internal_output_val;
  always_comb begin
    if (my_object_h == null) begin
      my_object_h = new();
      my_object_h.set_data(init_val);
    end else if (set_val_en) begin
      my_object_h.set_data(init_val);
    end
    internal_output_val = (my_object_h != null) ? my_object_h.get_data() : 8'd0;
  end
  assign current_read_val = internal_output_val;
endmodule
module DataStructures (
  input logic [7:0] val_to_add,
  input logic add_en,
  input logic rm_en,
  input int idx_assoc,
  output logic [7:0] queue_front_val,
  output logic [7:0] assoc_val_out
);
  logic [7:0] dyn_arr[];
  logic [7:0] queue_q[$];
  logic [7:0] assoc_arr[int];
  logic [7:0] temp_q_val;
  logic [7:0] temp_assoc_val;
  always_comb begin
    temp_q_val = 8'd0;
    if (add_en) begin
      queue_q.push_back(val_to_add);
    end
    if (rm_en && queue_q.size() > 0) begin
      void' (queue_q.pop_front());
    end
    if (queue_q.size() > 0) begin
      temp_q_val = queue_q[0];
    end
    queue_front_val = temp_q_val;
    temp_assoc_val = 8'd0;
    if (idx_assoc inside {[0:100]}) begin
      if (add_en) begin
        assoc_arr[idx_assoc] = val_to_add;
      end
      if (assoc_arr.exists(idx_assoc)) begin
        temp_assoc_val = assoc_arr[idx_assoc];
      end
    end
    assoc_val_out = temp_assoc_val;
    dyn_arr = new [1];
    if (dyn_arr.size() > 0) begin
      dyn_arr[0] = val_to_add;
    end
  end
endmodule
module FuncTaskModule (
  input logic [7:0] operand_a,
  input logic [7:0] operand_b,
  input logic select_op,
  output logic [8:0] func_result_out,
  output logic task_flag_out
);
  function automatic logic [8:0] my_adder_func (
    input logic [7:0] val1,
    input logic [7:0] val2
  );
    return val1 + val2;
  endfunction
  task automatic my_flag_task (
    input logic op_sel,
    output logic flag_out
  );
    if (op_sel) begin
      flag_out = 1'b1;
    end else begin
      flag_out = 1'b0;
    end
  endtask
  logic [8:0] local_func_res;
  logic local_task_flag;
  always_comb begin
    if (select_op) begin
      local_func_res = my_adder_func(operand_a, operand_b);
    end else begin
      local_func_res = my_adder_func(operand_a, operand_a);
    end
    func_result_out = local_func_res;
    my_flag_task(select_op, local_task_flag);
    task_flag_out = local_task_flag;
  end
endmodule
module UnionRealModule (
  input logic [31:0] float_in_bits_32,
  input logic [63:0] raw_input_64,
  output logic [63:0] union_out_64,
  output real real_out_val
);
  typedef union packed {
    logic [63:0] bits_val;
    longint      longint_val;
  } my_packed_union_t;
  my_packed_union_t u_instance;
  real r_converted_from_32bit_float;
  real r_calc;
  always_comb begin
    r_converted_from_32bit_float = real'(float_in_bits_32);
    r_calc = r_converted_from_32bit_float + 1.25;
    u_instance.bits_val = raw_input_64;
    union_out_64 = u_instance.longint_val;
    real_out_val = r_calc;
  end
endmodule
