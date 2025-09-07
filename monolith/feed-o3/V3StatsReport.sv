module stats_sumit_mod #(parameter WIDTH = 8, REPS = 16)
   (input  logic [WIDTH-1:0]               din,
    output logic [WIDTH*REPS-1:0]          dout);
   genvar i;
   generate
      for (i = 0; i < REPS; i++) begin : g_rep
         assign dout[i*WIDTH +: WIDTH] = din;
      end
   endgenerate
endmodule
module stats_stars_mod
   (input  logic [3:0]  in_a,
    input  logic [7:0]  in_b,
    output logic [11:0] out_sum);
   typedef struct packed {
      logic [3:0] a;
      logic [7:0] b;
   } my_struct_t;
   my_struct_t s;
   always_comb begin
      s       = '{a: in_a, b: in_b};
      out_sum = s.a + s.b;
   end
endmodule
module stats_stages_mod
   (input  logic clk,
    input  logic rst_n,
    input  logic start,
    output logic done);
   typedef enum logic [1:0] {IDLE, RUN, DONE_ST, ERR} state_t;
   state_t state, next_state;
   always_comb begin
      unique case (state)
         IDLE    : next_state = start ? RUN : IDLE;
         RUN     : next_state = DONE_ST;
         DONE_ST : next_state = IDLE;
         default : next_state = ERR;
      endcase
   end
   always_ff @(posedge clk or negedge rst_n) begin
      if (!rst_n) state <= IDLE;
      else        state <= next_state;
   end
   assign done = (state == DONE_ST);
endmodule
module stats_getStatSum_mod
   (input  logic [15:0] in_x,
    input  logic [15:0] in_y,
    output logic [15:0] sum_out);
   function automatic logic [15:0] f_add (input logic [15:0] a, b);
      f_add = a + b;
   endfunction
   always_comb sum_out = f_add(in_x, in_y);
endmodule
module stats_addStat_mod
  #(parameter DEPTH = 8)
   (input  logic                         clk,
    input  logic                         wr_en,
    input  logic [$clog2(DEPTH)-1:0]     index,
    input  logic [7:0]                   din,
    output logic [15:0]                  sum_out);
   logic [7:0] mem [0:DEPTH-1];
   always_ff @(posedge clk) begin
      if (wr_en) mem[index] <= din;
   end
   integer j;
   always_comb begin
      sum_out = 0;
      for (j = 0; j < DEPTH; j++) begin
         sum_out += mem[j];
      end
   end
endmodule
module stats_statsStage_mod
   (input  logic        clk,
    input  logic        start,
    input  logic        stop,
    output logic [31:0] elapsed);
   logic [31:0] counter;
   always_ff @(posedge clk) begin
      if (start)                counter <= 0;
      else if (!stop)           counter <= counter + 1;
   end
   assign elapsed = counter;
endmodule
module stats_infoHeader_mod
  #(parameter string VERSION = "v1.0")
   (input  logic in_sig,
    output logic out_sig);
   localparam string HEADER = {"Module Version: ", VERSION};
   assign out_sig = in_sig;
endmodule
module stats_statsReport_mod
   (input  logic [31:0] in_word,
    output logic [31:0] out_word);
   union packed {
      logic [31:0]                              word;
      struct packed { logic [15:0] low, high; } parts;
   } converter;
   always_comb begin
      converter.word = in_word;
      out_word       = {converter.parts.high, converter.parts.low};
   end
endmodule
module stats_summaryReport_mod
   (input  logic [7:0] a,
    input  logic [7:0] b,
    output logic [8:0] sum);
   class add_c;
      function int add (input int x, y);
         return x + y;
      endfunction
   endclass
   always_comb begin
      add_c c = new();
      sum = c.add(a, b);
   end
endmodule
