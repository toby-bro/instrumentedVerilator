module XConstantProcessing (
  input  logic [3:0] in_x_val_i,
  input  logic [3:0] in_x_mask_i,
  output logic [3:0] out_x_const_o,
  output logic        eq_case_o,
  output logic        neq_case_o
);
  assign out_x_const_o = 4'b1X0Z;
  assign eq_case_o = in_x_val_i ==? 4'b10X1;
  assign neq_case_o = in_x_mask_i !=? 4'b0X10;
endmodule
module BitSliceAndArraySel (
  input  logic        clk_i,
  input  logic        rst_n_i,
  input  logic [7:0]  data_in_i,
  input  int          index_i,
  input  logic        enable_i,
  input  logic [3:0]  write_val_i,
  output logic [3:0]  selected_bits_o,
  output logic [3:0]  array_val_o,
  output logic [3:0]  mod_array_val_o,
  output logic [7:0]  array_mem_o
);
  logic [3:0] internal_unpacked_array [0:2];
  logic [7:0] internal_packed_reg;
  always_ff @(posedge clk_i or negedge rst_n_i) begin
    if (!rst_n_i) begin
      internal_packed_reg <= 8'h00;
      for (int i=0; i<3; i++) begin
        internal_unpacked_array[i] <= 4'h0;
      end
    end else begin
      internal_packed_reg <= data_in_i;
      if (index_i >= 0 && index_i <= 4) begin
        internal_packed_reg[index_i+:4] <= write_val_i;
      end
      if (enable_i) begin
        if (index_i >= 0 && index_i <= 2) begin
          internal_unpacked_array[index_i] <= write_val_i;
        end
      end
    end
  end
  assign selected_bits_o = internal_packed_reg[index_i+:4];
  assign array_val_o = internal_unpacked_array[index_i];
  assign mod_array_val_o = internal_unpacked_array[index_i % 3];
  assign array_mem_o = internal_packed_reg;
endmodule
module SystemTasksAndWildcard (
  input  logic [7:0] check_val_i,
  output logic       is_unknown_o,
  output logic [3:0] count_bits_o,
  output logic       eq_wild_o,
  output logic       neq_wild_o
);
  assign is_unknown_o = $isunknown(check_val_i);
  assign count_bits_o = $countbits(check_val_i, 8'b1X1Z, 8'b0110, 8'bZ0X1);
  assign eq_wild_o = check_val_i == 8'b10X1Z0X1;
  assign neq_wild_o = check_val_i != 8'b0X1Z10X1;
endmodule
module ProceduralAssignmentsAndCases (
  input  logic [1:0] sel_i,
  input  logic [3:0] val_a_i,
  input  logic [3:0] val_b_i,
  output logic [3:0] case_out_o,
  output logic [3:0] final_val_o
);
  logic [3:0] temp_val;
  always_comb begin
    case (sel_i)
      2'b0X: case_out_o = val_a_i;
      2'b10: case_out_o = val_b_i;
      default: case_out_o = 4'b0000;
    endcase
    temp_val = val_a_i + val_b_i;
  end
  assign final_val_o = temp_val;
endmodule
module ClassInstantiationModule (
  input  logic        clk_i,
  input  logic        rst_n_i,
  input  int          init_val_i,
  input  logic [3:0]  class_in_i,
  output int          class_out_o
);
  class MyData;
    int data_member;
    function new(int val);
      data_member = val;
    endfunction
    function int process(logic [3:0] in_val);
      data_member = data_member + in_val;
      return data_member;
    endfunction
  endclass
  MyData my_instance;
  always_ff @(posedge clk_i or negedge rst_n_i) begin
    if (!rst_n_i) begin
      my_instance = null; 
      class_out_o <= 0;
    end else begin
      if (my_instance == null) begin
        my_instance = new(init_val_i);
      end
      class_out_o <= my_instance.process(class_in_i);
    end
  end
endmodule
