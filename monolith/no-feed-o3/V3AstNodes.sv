interface simple_if;
    logic sig;
    modport mp (input sig);
endinterface
module m_basic
  #(parameter WIDTH = 8)
  (input  logic [WIDTH-1:0] in_data,
   output logic [WIDTH-1:0] out_data);
   typedef struct packed {
       logic [3:0] nibble0;
       logic [3:0] nibble1;
   } nibbles_t;
   typedef union packed {
       nibbles_t n;
       logic [7:0] as_byte;
   } union_t;
   union_t u;
   always_comb begin
       u.as_byte = in_data;
       out_data  = (in_data != 0) ? {4'h0, u.n.nibble0} : {4'h0, u.n.nibble1};
   end
endmodule
module m_enum
   (input  logic [3:0] sel,
    output logic       flag);
   typedef enum logic [3:0] {IDLE=0, RUN=1, DONE=2, ERR=3} state_e;
   state_e s;
   always_comb begin
      unique case (sel)
         4'd0: s = IDLE;
         4'd1: s = RUN;
         4'd2: s = DONE;
         default: s = ERR;
      endcase
      flag = (s inside {RUN,DONE});
   end
endmodule
module m_arrays
   (input  logic       clk,
    input  logic [7:0] in_val,
    output logic [7:0] out_val);
   logic [3:0][1:0] packed_array;            
   logic [7:0]      unpacked_array [0:3];    
   int              dyn_array[];             
   int              q_data[$];               
   int              aa[string];              
   always_ff @(posedge clk) begin
       packed_array = {in_val[1:0], in_val[3:2], in_val[5:4], in_val[7:6]};
       unpacked_array[0] <= in_val;
       if (dyn_array.size() == 0) dyn_array = new[4];
       dyn_array[0] = in_val;
       q_data.push_back(in_val);
       aa["key"] = in_val;
       out_val <= unpacked_array[0];
   end
endmodule
module m_class
   (input  logic       clk,
    input  logic       trigger,
    output logic [31:0] result);
   class counter_c;
       rand int count;
       constraint rng { count inside {[0:100]}; }
       function void inc(); count++; endfunction
       function int  val(); return count; endfunction
   endclass
   counter_c c;
   always_ff @(posedge clk) begin
       if (c == null) c = new();
       if (trigger) c.inc();
       result <= c.val();
   end
endmodule
module m_clocking
   (input  logic clk,
    input  logic din,
    output logic dout);
   clocking cb @(posedge clk);
       default input #0 output #0;
       input  din;
       output dout;
   endclocking
   always_comb dout = cb.din;
endmodule
module m_vi
   (input  logic dummy,
    output logic out);
   virtual simple_if.mp vif;
   always_comb begin
       if (vif != null)
           out = vif.sig;
       else
           out = dummy;
   end
endmodule
module m_event
   (input  logic a,
    output logic b);
   event ev;
   always_comb begin
       b = a;
       -> ev;
   end
endmodule
module m_assert
   (input logic clk,
    input logic reset_n,
    input logic sig,
    output logic pass_through);
   assign pass_through = sig;
   property p_always_low;
       @(posedge clk) disable iff (!reset_n) sig == 1'b0;
   endproperty
   assert property (p_always_low);
   cover  property (p_always_low);
endmodule
module m_nettypes
   (input  logic drive,
    output tri   state_line);
    tri1 pullup_net;
    tri0 pulldown_net;
    assign pullup_net   = drive;
    assign pulldown_net = drive;
    assign state_line   = pullup_net & pulldown_net;
endmodule
module m_timescale
   (input  logic sig_in,
    output logic sig_out);
    timeunit 1ns;
    timeprecision 1ps;
    assign sig_out = sig_in;
endmodule
