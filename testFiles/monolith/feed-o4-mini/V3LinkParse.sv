class cls1;
   rand bit [3:0] a;
   rand bit [3:0] b;
   constraint c_a_less_b { a < b; }
endclass
package pkg1;
   typedef logic [7:0] pkg_t;
endpackage
interface if1;
   logic sig;
   modport mp (input sig);
endinterface
module m_data_types(input logic [1:0] sel, output logic [3:0] out);
   typedef enum logic [1:0] { E0 = 2'd0, E1 = 2'd1, E2 = 2'd2, E3 = 2'd3 } enum_t;
   typedef struct packed { logic [3:0] sdata; logic sflag; } st_t;
   typedef union packed { logic [3:0] udata; logic [3:0] uflag; } un_t;
   enum_t ev;
   st_t sv;
   un_t uv;
   assign sv.sdata = sel ? 4'hA : 4'h5;
   assign sv.sflag = sel[0];
   assign uv.udata = sv.sdata;
   assign out = {ev, sv.sflag, uv.uflag};
endmodule
module m_loops(input logic [3:0] arr [3:0], output logic flag);
   int i;
   always_comb begin
      flag = 1'b0;
      foreach(arr[i]) begin
         if (arr[i] == 4'b0000)
            flag = 1'b1;
      end
      repeat (2) begin
         flag = flag || (arr[0] != 4'b0000);
      end
      i = 0;
      do begin
         flag = flag && (arr[i] != 4'b0000);
         i = i + 1;
      end while (i < 4);
      i = 0;
      while (i < 4) begin
         flag = flag ^ (arr[i] != 4'b0000);
         i = i + 1;
      end
   end
endmodule
module m_generate_blocks #(parameter PSEL = 1, parameter logic [1:0] PCS = 2'b00)
   (input logic sel, input logic [1:0] cs, output logic o1, output logic o2);
   logic tmp_arr [0:1];
   genvar gi;
   generate
      if (PSEL) begin: gen_if
         assign o1 = 1'b1;
      end else begin: gen_else
         assign o1 = 1'b0;
      end
      for (gi = 0; gi < 2; gi = gi + 1) begin: gen_for
         case (PCS)
            2'b00: begin: case0
               assign tmp_arr[gi] = 1'b1;
            end
            default: begin: case_def
               assign tmp_arr[gi] = 1'b0;
            end
         endcase
      end
   endgenerate
   assign o2 = tmp_arr[0] & tmp_arr[1];
endmodule
module m_task_func(input logic clk, input logic rst, output logic dout);
   import "DPI-C" function void dpi_invoke(input int v);
   function automatic int f_compute(input int a);
      int b;
      b = a + 1;
      return b;
   endfunction
   task automatic t_process(input int a, output int b);
      b = a * 2;
   endtask
   always_ff @(posedge clk) begin
      if (rst)
         dout <= 1'b0;
      else begin
         dpi_invoke(dout);
         dout <= f_compute(dout);
      end
   end
endmodule
module m_clocking(input logic clk, input logic din, input logic ein, output logic data, output logic en);
   clocking cb @(posedge clk);
      input din;
      input ein;
      output data;
      output en;
   endclocking
   always @(cb) begin
      data <= cb.din;
      en <= cb.ein;
   end
endmodule
module m_event_control(input logic a, input logic b, output logic or_out, output logic and_out);
   always @* begin
      or_out = a || b;
   end
   always @(posedge a or negedge b) begin
      and_out = a && b;
   end
endmodule
module m_pkg_if(input pkg1::pkg_t in, output pkg1::pkg_t out);
   import pkg1::*;
   if1 if_inst();
   assign out = in + if_inst.sig;
endmodule
primitive udp1 (out, in1, in2);
   output out; input in1, in2;
   table
      1 1 : 1;
      1 0 : 0;
      0 1 : 0;
      0 0 : 0;
   endtable
endprimitive
module m_udp_inst(input in1, input in2, output out1, output out2);
   udp1 u1 (out1, in1, in2);
   udp1 u2 (out2, in1, in2);
   assign out1 = in1 & in2;
endmodule
module m_cover(input logic clk, input logic [3:0] cp, output logic done);
   covergroup cg @(posedge clk);
      coverpoint cp;
   endgroup
   assign done = 1'b0;
endmodule
module m_constraints(input logic clk, output logic done);
   always_ff @(posedge clk) begin
      cls1 c_inst = new();
      c_inst.randomize();
   end
   assign done = 1'b0;
endmodule
