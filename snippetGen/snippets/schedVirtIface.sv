class simple_data_class;
  int data_value;
  function new(int initial_value);
    this.data_value = initial_value;
    //INJECT
  endfunction
  function int get_data();
    //INJECT
    return this.data_value;
  endfunction
endclass
module mod_if_write_stmt (
    input bit condition,
    input logic [7:0] in_val,
    output logic [7:0] out_val,
    output logic flag
);
  always_comb begin
    out_val = '0;
    flag = '0;
    //INJECT
    if (condition) begin
      out_val = in_val + 1;
      flag = 1;
      //INJECT
    end else begin
      out_val = in_val - 1;
      flag = 0;
      //INJECT
    end
    //INJECT
  end
endmodule
module mod_while_write_stmt (
    input bit start,
    input logic [3:0] limit,
    output logic [3:0] count,
    output logic done
);
  always_comb begin
    logic [3:0] temp_count = '0;
    logic temp_done = 0;
    logic [3:0] loop_count = '0; 
    count = '0;
    done = 0;
    //INJECT
    if (start) begin
      loop_count = '0;
      while (loop_count < limit) begin
        loop_count = loop_count + 1;
        //INJECT
      end
      temp_count = loop_count;
      temp_done = 1;
      //INJECT
    end else begin
       temp_count = '0;
       temp_done = 0;
       //INJECT
    end
    count = temp_count;
    done = temp_done;
    //INJECT
  end
endmodule
module mod_case_write_stmt (
    input logic [1:0] sel,
    input logic [3:0] val1,
    input logic [3:0] val2,
    output logic [3:0] result
);
  always_comb begin
    result = 'x;
    //INJECT
    case (sel)
      2'b00: begin
        result = val1;
        //INJECT
      end
      2'b01: begin
        result = val2;
        //INJECT
      end
      default: begin
        result = '0;
        //INJECT
      end
    endcase
    //INJECT
  end
endmodule
module mod_blocking_assign (
    input logic [4:0] in_a,
    input logic [4:0] in_b,
    output logic [4:0] out_c
);
  always_comb begin
    //INJECT
    out_c = in_a + in_b;
    //INJECT
  end
endmodule
module mod_nonblocking_assign (
    input bit clk,
    input logic [4:0] in_d,
    output logic [4:0] out_e
);
  always_ff @(posedge clk) begin
    //INJECT
    out_e <= in_d;
    //INJECT
  end
endmodule
module mod_task_write (
    input bit en,
    input logic [2:0] in_f,
    output logic [2:0] out_g,
    output bit status
);
  task automatic update_output;
    input logic [2:0] value;
    output logic [2:0] result_val;
    output bit status_flag;
    begin
      result_val = value * 2;
      status_flag = (value > 0);
      //INJECT
    end
  endtask
  always_comb begin
    out_g = '0;
    status = 0;
    //INJECT
    if (en) begin
      update_output(in_f, out_g, status);
      //INJECT
    end
    //INJECT
  end
endmodule
module mod_function_write (
    input bit enable_process,
    input logic [3:0] in_h,
    output logic [3:0] out_i
);
  function automatic logic [3:0] calculate_value;
    input logic [3:0] operand;
    begin
      logic [3:0] modified_operand;
      modified_operand = operand + 1;
      //INJECT
      return modified_operand;
    end
  endfunction
  always_comb begin
    out_i = '0;
    //INJECT
    if (enable_process) begin
      out_i = calculate_value(in_h);
      //INJECT
    end
    //INJECT
  end
endmodule
module mod_nested_blocks (
    input bit gate_a,
    input bit gate_b,
    input logic [5:0] data_in,
    output logic [5:0] data_out
);
  always_comb begin
    logic [5:0] temp1 = '0;
    logic [5:0] temp2 = '0;
    logic [5:0] final_data_out = 'x;
    data_out = 'x;
    //INJECT
    temp1 = data_in;
    //INJECT
    if (gate_a) begin : block_level2
      temp2 = temp1 + 1;
      //INJECT
      if (gate_b) begin : block_level3
         final_data_out = temp2 - 1;
         //INJECT
      end else begin
         final_data_out = temp2;
         //INJECT
      end
    end else begin
       final_data_out = temp1;
       //INJECT
    end
    data_out = final_data_out;
    //INJECT
  end
endmodule
module mod_always_ff_timing (
    input bit clk,
    input bit sync_in,
    output logic sync_out
);
  always_ff @(posedge clk) begin
    //INJECT
    sync_out <= sync_in;
    //INJECT
  end
endmodule
module mod_class_instantiation (
    input bit enable_create,
    input int initial_val_in,
    output int result_val_out
);
  simple_data_class my_obj;
  always_comb begin
    result_val_out = 0;
    my_obj = null;
    //INJECT
    if (enable_create) begin
      my_obj = new(initial_val_in);
      //INJECT
    end else begin
      my_obj = null;
      //INJECT
    end
    if (my_obj != null) begin
      result_val_out = my_obj.get_data();
      //INJECT
    end else begin
      result_val_out = -1;
      //INJECT
    end
    //INJECT
  end
endmodule
