module basic_assign(input logic [7:0] a, output logic [7:0] b);
  assign b = a;
endmodule
module event_control(input logic clk, input logic rst, output logic q);
  event ev;
  always @(posedge clk) begin
    -> ev;
  end
  always @(ev or rst) begin
    if (rst) q <= 0;
    else q <= 1;
  end
endmodule
module wait_module(input logic clk, input logic [7:0] data, output logic done);
  always @(posedge clk) begin
    wait (data == 8'hFF);
    done <= 1'b1;
  end
endmodule
module fork_module(input logic [7:0] data, output logic [7:0] out1, output logic [7:0] out2);
  always @(*) begin
    fork
      begin out1 = data; end
      begin out2 = data + 1; end
    join_none;
  end
endmodule
module join_all_module(input logic [7:0] data, output logic [7:0] sum);
  logic [7:0] a, b;
  always @(*) begin
    fork
      begin a = data; end
      begin b = data + 2; end
    join;
    sum = a + b;
  end
endmodule
module join_any_module(input logic [7:0] data, output logic [7:0] first_result);
  logic [7:0] r1, r2;
  always @(*) begin
    fork
      begin r1 = data + 3; end
      begin r2 = data + 5; end
    join_any;
    first_result = r1;
  end
endmodule
module class_module(input logic clk, input logic [7:0] d, output logic [7:0] y);
  class C;
    int a;
    function void set_val(int v);
      a = v;
    endfunction
    function int get_val();
      return a;
    endfunction
  endclass
  C obj;
  always @(posedge clk) begin
    obj = new();
    obj.set_val(d);
    y <= obj.get_val();
  end
endmodule
module task_module(input logic clk, input logic [7:0] in_data, output logic [7:0] out_data);
  task automatic compute(input logic [7:0] a, output logic [7:0] b);
    if (a > 0) wait (a > 8);
    b = a * 2;
  endtask
  logic [7:0] tmp;
  always @(posedge clk) begin
    compute(in_data, tmp);
    out_data <= tmp;
  end
endmodule
module function_module(input logic [7:0] a, input logic [7:0] b, output logic [7:0] sum_ab);
  function automatic logic [7:0] add2(input logic [7:0] x, input logic [7:0] y);
    add2 = x + y;
  endfunction
  always @(*) begin
    sum_ab = add2(a, b);
  end
endmodule
module generate_module(input logic [3:0] in_bits, output logic [3:0] out_bits);
  genvar i;
  generate
    for (i = 0; i < 4; i = i + 1) begin : gen_loop
      assign out_bits[i] = in_bits[i];
    end
  endgenerate
endmodule
module disable_fork_module(input logic clk, input logic start, output logic result);
  always @(posedge clk) begin
    fork : F
      begin wait(start); result <= 1'b1; end
      begin wait(!start); result <= 1'b0; end
    join_any;
    disable F;
  end
endmodule
