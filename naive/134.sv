module Module_BasicLogic(
  input  logic [7:0] in_a,
  input  logic [7:0] in_b,
  input  logic       select_op,
  output logic [7:0] out_result
);
  logic [7:0] temp_sum;
  logic [7:0] temp_diff;
  always_comb begin
    temp_sum  = in_a + in_b;
    temp_diff = in_a - in_b;
    if (select_op) begin
      out_result = temp_sum;
    end else begin
      out_result = temp_diff;
    end
  end
endmodule
module Module_Sequential(
  input  logic       clk,
  input  logic       rst_n,
  input  logic       data_in,
  output logic [3:0] shifted_data_out
);
  logic [3:0] s_reg;
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      s_reg <= 4'b0;
    end else begin
      s_reg <= {s_reg[2:0], data_in}; 
    end
  end
  assign shifted_data_out = s_reg;
endmodule
module Module_CaseParam(
  input  logic [1:0] op_code,
  input  logic [7:0] operand1,
  input  logic [7:0] operand2,
  output logic [7:0] result_val
);
  parameter ADD = 2'b00;
  parameter SUB = 2'b01;
  parameter AND = 2'b10;
  parameter OR  = 2'b11;
  always_comb begin
    case (op_code)
      ADD: result_val = operand1 + operand2;
      SUB: result_val = operand1 - operand2;
      AND: result_val = operand1 & operand2;
      OR:  result_val = operand1 | operand2;
      default: result_val = 8'hFF; 
    endcase
  end
endmodule
module Module_StructFunc(
  input  logic [7:0] input_data,
  output logic [7:0] processed_data
);
  typedef struct packed {
    logic [3:0] upper_nibble;
    logic [3:0] lower_nibble;
  } s_byte_t;
  function automatic logic [7:0] manipulate_byte(s_byte_t data_in_struct);
    s_byte_t temp_byte;
    temp_byte.upper_nibble = ~data_in_struct.lower_nibble;
    temp_byte.lower_nibble = data_in_struct.upper_nibble;
    return {temp_byte.upper_nibble, temp_byte.lower_nibble};
  endfunction
  s_byte_t input_struct;
  always_comb begin
    input_struct.upper_nibble = input_data[7:4];
    input_struct.lower_nibble = input_data[3:0];
    processed_data = manipulate_byte(input_struct);
  end
endmodule
module Module_EnumLocalparam(
  input  logic [1:0] current_state_code,
  input  logic       enable_op,
  output logic [2:0] next_state_indicator
);
  typedef enum logic [1:0] {
    STATE_IDLE  = 2'b00,
    STATE_READY = 2'b01,
    STATE_BUSY  = 2'b10,
    STATE_DONE  = 2'b11
  } fsm_state_t;
  localparam INITIAL_INDICATOR = 3'b001;
  localparam BUSY_INDICATOR    = 3'b010;
  localparam DONE_INDICATOR    = 3'b100;
  fsm_state_t current_state_enum;
  always_comb begin
    current_state_enum = fsm_state_t'(current_state_code); 
    if (!enable_op) begin
      next_state_indicator = INITIAL_INDICATOR;
    end else begin
      case (current_state_enum)
        STATE_IDLE:  next_state_indicator = INITIAL_INDICATOR;
        STATE_READY: next_state_indicator = INITIAL_INDICATOR;
        STATE_BUSY:  next_state_indicator = BUSY_INDICATOR;
        STATE_DONE:  next_state_indicator = DONE_INDICATOR;
        default:     next_state_indicator = INITIAL_INDICATOR; 
      endcase
    end
  end
endmodule
class SimpleProcessor;
  logic [7:0] data_storage;
  function new();
    data_storage = 8'h00; 
  endfunction
  function void set_data(logic [7:0] in_val);
    data_storage = in_val;
  endfunction
  function logic [7:0] process_data();
    return data_storage + 1; 
  endfunction
endclass
module Module_ClassInst(
  input  logic [7:0] class_input_val,
  output logic [7:0] class_output_val
);
  SimpleProcessor my_processor;
  always_comb begin
    my_processor = new(); 
    my_processor.set_data(class_input_val);
    class_output_val = my_processor.process_data();
  end
endmodule
module Module_TaskForkJoin(
  input  logic [7:0] task_in_val,
  input  logic       task_enable,
  output logic [7:0] task_out_val
);
  logic [7:0] internal_calc_a;
  logic [7:0] internal_calc_b;
  task automatic perform_concurrent_ops(input logic [7:0] val_a, input logic [7:0] val_b, output logic [7:0] result_c);
    fork
      begin 
        internal_calc_a = val_a + 2;
      end
      begin 
        internal_calc_b = val_b * 2;
      end
    join_none 
    result_c = internal_calc_a + internal_calc_b; 
  endtask
  always_comb begin
    if (task_enable) begin
      perform_concurrent_ops(task_in_val, task_in_val + 1, task_out_val);
    end else begin
      task_out_val = 8'h00;
    end
  end
endmodule
