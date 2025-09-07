module class_inheritance_mod
  ( input  logic        clk,
    input  logic        rst_n,
    input  logic [7:0]  din,
    output logic [7:0]  dout );
   interface class IProcessor;
      pure virtual function void process
         ( input  logic [7:0] data ,
           output logic [7:0] res  );
   endclass
   class BaseClass;
      static int global_counter;
      function new();
         global_counter = 0;
      endfunction
      static function void inc();
         global_counter++;
      endfunction
   endclass
   class DerivedClass extends BaseClass implements IProcessor;
      typedef struct packed {
         logic [3:0] header;
         logic [7:0] payload;
      } Packet_t;
      typedef struct packed {
         Packet_t     pkt;
         logic [7:0]  crc;
      } Frame_t;
      typedef union packed {
         Frame_t      frame;
         logic [19:0] raw;
      } Data_u;
      static task run_static ( input logic [7:0] val );
         global_counter += val;
      endtask
      function automatic Frame_t make_frame ( input logic [7:0] d );
         Frame_t f;
         f.pkt.header  = d[7:4];
         f.pkt.payload = d;
         f.crc         = ~d;
         return f;
      endfunction
      virtual function void process
         ( input  logic [7:0] data ,
           output logic [7:0] res  );
         Frame_t fr = make_frame(data);
         res = fr.crc;
      endfunction
   endclass
   import "DPI-C" function int cfunc ( input int x );
   DerivedClass dc_h;
   property always_active;
      @(posedge clk) disable iff (!rst_n) din == din;
   endproperty
   cover property (always_active);
   always_ff @(posedge clk or negedge rst_n) begin
      if (!rst_n) begin
         dc_h = new();
         dout <= '0;
      end
      else if (dc_h != null) begin
         dc_h.process(din, dout);
         DerivedClass::run_static(din);
      end
   end
endmodule
module task_feature_mod
  ( input  logic        clk,
    input  logic [3:0]  a ,
    input  logic [3:0]  b ,
    output logic [4:0]  sum );
   task static add_static
      ( input  logic [3:0] x ,
        input  logic [3:0] y ,
        output logic [4:0] z );
      z = x + y;
   endtask
   task automatic passthru
      ( input  logic [4:0] in  ,
        output logic [4:0] out );
      out = in;
   endtask
   always_ff @(posedge clk) begin
      logic [4:0] tmp;
      add_static ( a , b , tmp );
      passthru   ( tmp , sum );
   end
endmodule
module typedef_union_mod
  ( input  logic         sel,
    input  logic  [15:0] in_bus,
    output logic  [15:0] out_bus );
   typedef struct packed {
      logic [7:0] hi;
      logic [7:0] lo;
   } word_t;
   typedef union packed {
      word_t       w;
      logic [15:0] vec;
   } word_u;
   word_u data_u;
   always_comb begin
      data_u.vec = in_bus;
      out_bus = sel ? {8'h0, data_u.w.hi} : {8'h0, data_u.w.lo};
   end
endmodule
module simple_class_mod
  ( input  logic        trig ,
    output logic [31:0] value );
   class Simple;
      typedef struct packed {
         logic [31:0] data;
      } Data_t;
      function automatic Data_t id ( input Data_t d );
         return d;
      endfunction
   endclass
   Simple s_h;
   always_comb begin
      Simple::Data_t d_tmp;
      if (trig) begin
         s_h = new();
         d_tmp.data = 32'hCAFE_BABE;
         value = s_h.id(d_tmp).data;
      end
      else begin
         value = '0;
      end
   end
endmodule
