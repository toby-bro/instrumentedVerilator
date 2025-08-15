interface simple_if #(parameter DATA_WIDTH = 8);
  logic [DATA_WIDTH-1:0] data_in;
  logic [DATA_WIDTH-1:0] data_out;
  logic enable;
  logic done;
  modport master (input data_out, output data_in, output enable, input done);
  modport slave (input data_in, output data_out, input enable, output done);
endinterface
interface another_if;
  logic [3:0] val_a;
  logic [3:0] val_b;
  modport producer (output val_a, input val_b);
  modport consumer (input val_a, output val_b);
endinterface
module VirtIfaceAssigns (
  input logic clk,
  input logic reset_n,
  input logic [7:0] in_data,
  output logic [7:0] out_result,
  simple_if.master vif_master
);
  logic [7:0] internal_reg;
  virtual simple_if.master vif_master_h;
  initial begin
    vif_master_h = vif_master;
  end
  always_ff @(posedge clk or negedge reset_n) begin
    if (!reset_n) begin
      vif_master_h.data_in <= '0;
      vif_master_h.enable <= 1'b0;
      internal_reg <= '0;
      out_result <= '0;
    end else begin
      vif_master_h.data_in <= in_data + 1;
      internal_reg <= vif_master_h.data_out;
      vif_master_h.enable <= 1'b1;
      out_result <= internal_reg;
      vif_master_h.data_in <= in_data + 2;
      vif_master_h.enable <= 1'b0;
    end
  end
endmodule
module VirtIfaceProcCalls (
  input logic clk,
  input logic reset,
  input logic [15:0] value_in,
  output logic [15:0] value_out,
  simple_if.slave vif_slave_proc
);
  logic temp_val;
  virtual simple_if.slave vif_slave_proc_h;
  initial begin
    vif_slave_proc_h = vif_slave_proc;
  end
  function automatic logic [15:0] write_and_read(input logic [15:0] data_to_write);
    vif_slave_proc_h.data_out <= data_to_write;
    vif_slave_proc_h.done <= 1'b1;
    return vif_slave_proc_h.data_in;
  endfunction
  task automatic update_interface(input logic [15:0] new_val);
    vif_slave_proc_h.data_out <= new_val + 5;
    vif_slave_proc_h.done <= 1'b0;
    temp_val <= vif_slave_proc_h.enable;
  endtask
  always_ff @(posedge clk) begin
    if (reset) begin
      value_out <= '0;
    end else begin
      value_out <= write_and_read(value_in);
      update_interface(value_in);
    end
  end
endmodule
module VirtIfaceControlFlow (
  input logic clk,
  input logic enable_processing,
  input logic [3:0] loop_count,
  input logic [7:0] data_to_process,
  output logic proc_done,
  simple_if.master vif_ctrl
);
  logic [7:0] current_data;
  logic loop_active;
  int i;
  virtual simple_if.master vif_ctrl_h;
  initial begin
    vif_ctrl_h = vif_ctrl;
  end
  always_ff @(posedge clk) begin
    proc_done <= 1'b0;
    loop_active <= 1'b0;
    current_data <= '0;
    if (enable_processing) begin
      vif_ctrl_h.data_in <= data_to_process;
      vif_ctrl_h.enable <= 1'b1;
      current_data <= vif_ctrl_h.data_out;
      if (vif_ctrl_h.done == 1'b0) begin 
        vif_ctrl_h.data_in <= 8'hAA;
      end else begin
        vif_ctrl_h.data_in <= 8'hBB;
      end
    end else begin
      vif_ctrl_h.data_in <= '0;
      vif_ctrl_h.enable <= 1'b0;
    end
    i <= 0;
    while (i < loop_count) begin 
      logic [7:0] calculated_data_in = current_data + i;
      if (calculated_data_in != '0) begin 
        vif_ctrl_h.data_in <= calculated_data_in;
        vif_ctrl_h.enable <= 1'b0;
        loop_active <= 1'b1;
        i <= i + 1;
        if (i == 2) begin
          break;
        end
      end else begin
        break; 
      end
    end
    for (int j = 0; j < 2; j++) begin
      vif_ctrl_h.data_in <= data_to_process + j;
    end
    proc_done <= 1'b1;
  end
endmodule
module VirtIfaceMultiType (
  input logic clk,
  input logic reset,
  input logic [7:0] in_val,
  output logic [7:0] out_val,
  simple_if.master simple_vif,
  another_if.producer another_vif
);
  logic [7:0] temp_val_simp;
  logic [3:0] temp_val_another;
  virtual simple_if.master simple_vif_h;
  virtual another_if.producer another_vif_h;
  initial begin
    simple_vif_h = simple_vif;
    another_vif_h = another_vif;
  end
  always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
      simple_vif_h.data_in <= '0;
      simple_vif_h.enable <= 1'b0;
      another_vif_h.val_a <= '0;
      out_val <= '0;
    end else begin
      simple_vif_h.data_in <= in_val;
      simple_vif_h.enable <= 1'b1;
      temp_val_simp <= simple_vif_h.data_out + 1;
      another_vif_h.val_a <= temp_val_simp[3:0];
      temp_val_another <= another_vif_h.val_b;
      simple_vif_h.data_in <= {temp_val_another, temp_val_another};
      simple_vif_h.enable <= 1'b0;
      out_val <= simple_vif_h.data_out;
    end
  end
endmodule
module VirtIfaceComplexExpr (
  input logic clk,
  input logic start,
  input logic [1:0] sel,
  output logic [7:0] result,
  simple_if.master complex_vif
);
  logic [7:0] temp_res;
  virtual simple_if.master complex_vif_h;
  initial begin
    complex_vif_h = complex_vif;
  end
  always_ff @(posedge clk) begin
    if (start) begin
      temp_res <= complex_vif_h.data_out + (complex_vif_h.enable ? 8'hFF : 8'h00);
      case (sel)
        2'b00: begin
          complex_vif_h.data_in <= temp_res;
        end
        2'b01: begin
          complex_vif_h.data_in <= temp_res + 1;
        end
        2'b10: begin
          if (complex_vif_h.data_out > 5) begin
            complex_vif_h.data_in <= 8'h11;
          end else begin
            complex_vif_h.data_in <= 8'h22;
          end
        end
        default: begin
          complex_vif_h.data_in <= 8'hFF;
          for (int k = 0; k < 3; k++) begin
            complex_vif_h.data_in <= complex_vif_h.data_out + k;
            if (k == 1) begin
              complex_vif_h.enable <= 1'b1;
            end
          end
        end
      endcase
      result <= temp_res;
    end else begin
      result <= '0;
      complex_vif_h.data_in <= '0;
      complex_vif_h.enable <= '0;
    end
  end
endmodule
