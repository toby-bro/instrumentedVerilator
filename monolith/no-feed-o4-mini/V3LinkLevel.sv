timeunit 1ns; timeprecision 1ps;
class Sorter;
  function void sort(ref logic [7:0] in_arr [0:3], ref logic [7:0] out_arr [0:3]);
    logic [7:0] temp_arr [0:3];
    for (int i = 0; i < 4; i++) temp_arr[i] = in_arr[i];
    for (int i = 0; i < 4; i++)
      for (int j = 0; j < 3; j++)
        if (temp_arr[j] > temp_arr[j+1]) begin
          logic [7:0] t = temp_arr[j];
          temp_arr[j] = temp_arr[j+1];
          temp_arr[j+1] = t;
        end
    for (int i = 0; i < 4; i++) out_arr[i] = temp_arr[i];
  endfunction
endclass
interface SimpleIface #(int WIDTH = 8)(input logic clk);
  logic [WIDTH-1:0] data;
endinterface
module mod_sort_by_level(input  logic          clk,
                         input  logic [7:0]  in_arr  [0:3],
                         output logic [7:0]  sorted_arr [0:3]);
  always_ff @(posedge clk) begin
    Sorter s = new();
    s.sort(in_arr, sorted_arr);
  end
endmodule
module time_scaling(input  logic clk,
                    input  logic rst,
                    output logic tick);
  timeunit 1us; timeprecision 10ns;
  always_ff @(posedge clk or posedge rst)
    if (rst) tick <= 1'b0;
    else     tick <= ~tick;
endmodule
module childmod(input  logic a,
                output logic z);
  assign z = ~a;
endmodule
module wrap_top(input  logic a1,
                input  logic a2,
                output logic z1,
                output logic z2);
  wire w1, w2;
  childmod u1(.a(a1), .z(w1));
  childmod u2(.a(a2), .z(w2));
  assign z1 = w1;
  assign z2 = w2;
endmodule
module wrap_top_cell(input  logic        clk,
                     input  logic [3:0]  in,
                     output logic [3:0]  out);
  SimpleIface#(.WIDTH(4)) ifcs[2] (.clk(clk));
  genvar i;
  generate
    for (i = 0; i < 2; i++) begin : gen_ifc
      always_comb begin
        ifcs[i].data = in;
      end
    end
  endgenerate
  assign out = ifcs[1].data;
endmodule
