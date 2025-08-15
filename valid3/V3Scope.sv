package util_pkg;
   function automatic logic [3:0] add4 (input logic [3:0] a, b);
      add4 = a + b;
   endfunction
   import "DPI-C" function int c_add (input int a, input int b);
endpackage
interface simple_if (input logic clk);
   logic req, gnt;
   task automatic toggle ();
      req <= ~req;
   endtask
   always_ff @(posedge clk) begin
      gnt <= req;
   end
   modport mp (input req, output gnt, import task toggle);
endinterface
module mod_child (
   input  logic        clk,
   input  logic        rst,
   input  logic [7:0]  data_in,
   output logic [7:0]  data_out
);
   wire alias_bit = data_in[0];
   wire [7:0] alias_to_out;
   assign alias_to_out = data_in;
   task automatic invert (input  logic [7:0] a, output logic [7:0] b);
      b = ~a;
   endtask
   function automatic logic [7:0] add1 (input logic [7:0] a);
      add1 = a + 8'd1;
   endfunction
   property p_data;
      @(posedge clk) disable iff (rst) data_in[0];
   endproperty
   cover property (p_data);
   int int_sum;
   always_ff @(posedge clk) begin
      if (rst) begin
         data_out <= 8'd0;
      end else begin
         invert(data_in, data_out);
         cover (alias_bit);
         if (add1(data_in) == 8'd0) begin
            $error("%m : add1 produced zero");
         end
      end
      int_sum <= util_pkg::c_add(int'(data_in), int'(data_out));
   end
endmodule
module mod_parent (
   input  logic        clk,
   input  logic        rst,
   input  logic [7:0]  up_in,
   output logic [7:0]  up_out
);
   simple_if sif (clk);
   assign sif.req = up_in[0];
   assign up_out  = sif.gnt ? up_in : 8'd0;
   always_comb begin
      if (sif.gnt) begin
         sif.toggle();
      end
   end
   logic [7:0] child_out;
   mod_child u_child (
      .clk      (clk),
      .rst      (rst),
      .data_in  (up_in),
      .data_out (child_out)
   );
endmodule
module class_mod (
   input  logic [7:0] in_val,
   output logic [7:0] out_val
);
   class simple_class;
      function automatic int incr (int i);
         incr = i + 1;
      endfunction
   endclass
   simple_class c;
   always_comb begin
      if (c == null) c = new();
   end
   assign out_val = (c == null) ? 8'd0 : c.incr(in_val)[7:0];
endmodule
