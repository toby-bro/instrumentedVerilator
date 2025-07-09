package util_pkg;
   typedef enum logic [1:0] {
      S_IDLE,
      S_RUN ,
      S_DONE
   } state_e;
   typedef struct packed {
      logic [7:0] a;
      logic [7:0] b;
   } pair8_t;
   typedef union packed {
      logic [15:0] as_word;
      pair8_t      as_pair;
   } u_data_t;
endpackage
module delimit_gen_attr #(
   parameter int DEPTH = 4
) (
   input  logic                clk,
   input  logic [DEPTH-1:0]    in_bus,
   output logic [DEPTH-1:0]    out_bus
);
   (* keep = "true" *) logic [DEPTH-1:0] stage   [DEPTH-1:0];
   generate
      genvar gi, gj;
      for (gi = 0; gi < DEPTH; gi++) begin : G_LVL1
         for (gj = 0; gj < DEPTH; gj++) begin : G_LVL2
            always_ff @(posedge clk) begin
               stage[gi][gj] <= in_bus[gi] ^ in_bus[gj];
            end
         end
      end
   endgenerate
   always_comb begin
      out_bus = '0;
      for (int i = 0; i < DEPTH; i++)
         out_bus[i] = stage[i][i];
   end
   class c_accum;
      int total;
      function new(); total = 0; endfunction
      function void add(int v); total += v; endfunction
   endclass
   always_ff @(posedge clk) begin
      automatic c_accum acc = new();
      for (int i = 0; i < DEPTH; i++) acc.add(stage[i][i]);
   end
endmodule
module enum_case_proc (
   input  logic                clk,
   input  util_pkg::state_e    req_state,
   output logic                state_match
);
   util_pkg::state_e cur_state;
   util_pkg::state_e nxt_state;
   always_comb begin
      nxt_state = cur_state;
      unique case (req_state) inside
         util_pkg::S_IDLE : nxt_state = util_pkg::S_RUN ;
         util_pkg::S_RUN  : nxt_state = util_pkg::S_DONE;
         default          : nxt_state = util_pkg::S_IDLE;
      endcase
   end
   class c_cnt;
      util_pkg::state_e q[$];
      function void push(util_pkg::state_e v); q.push_back(v); endfunction
   endclass
   always_ff @(posedge clk) begin
      automatic c_cnt c = new();
      c.push(nxt_state);
      cur_state   <= nxt_state;
      state_match <= (cur_state == req_state);
   end
endmodule
module struct_union_pack #(
   parameter int WIDTH = 16
) (
   input  logic                    clk,
   input  util_pkg::u_data_t       din,
   output logic [WIDTH-1:0]        dout
);
   util_pkg::u_data_t local_u;
   class temp_c;
      int v;
      function new(int x); v = x; endfunction
   endclass
   always_ff @(posedge clk) begin
      automatic temp_c t;
      local_u <= din;
      dout    <= {local_u.as_pair.b, local_u.as_pair.a};
      t = new(int'(din.as_word));
   end
endmodule
module array_dyn_queue (
   input  logic        clk,
   input  logic [31:0] data_in,
   output logic [31:0] sum_out
);
   logic [31:0] dyn_array [];
   logic [31:0] queue_q   [$];
   logic [31:0] acc;
   always_ff @(posedge clk) begin
      dyn_array = new[dyn_array.size()+1];
      dyn_array[dyn_array.size()-1] = data_in;
      queue_q.push_back(data_in);
      acc = 0;
      for (int i = 0; i < dyn_array.size(); i++) acc += dyn_array[i];
      sum_out <= acc;
   end
endmodule
interface simple_if #(parameter int W = 8)(input logic clk);
   logic [W-1:0] a;
   logic [W-1:0] b;
   modport host (input a, output b);
endinterface
module interface_user #(
   parameter int W = 8
) (
   input  logic               clk,
   input  logic [W-1:0]       in_data,
   output logic [W-1:0]       out_data
);
   simple_if #(W) intf (clk);
   class holder #(type T = int);
      T val;
      function new(T v); val = v; endfunction
   endclass
   always_ff @(posedge clk) begin
      automatic holder#(logic [W-1:0]) h;
      intf.a <= in_data;
      intf.b <= in_data + 1;
      out_data <= intf.b;
      h = new(out_data);
   end
endmodule
module rand_nested_fn (
   input  logic       clk,
   output logic [7:0] rnd_val
);
   class c_rand;
      rand byte v;
      constraint c1 { v inside {[1:10]}; }
   endclass
   function automatic byte gen();
      c_rand cr = new();
      void'(cr.randomize());
      return cr.v;
   endfunction
   always_ff @(posedge clk) begin
      rnd_val <= gen();
   end
endmodule
module gen_if_empty #(
   parameter bit USE_REG = 1
) (
   input  logic clk,
   input  logic in_sig,
   output logic out_sig
);
   generate
      if (USE_REG) begin : GEN_REG
         logic r;
         always_ff @(posedge clk) begin
            r <= in_sig;
         end
         assign out_sig = r;
      end
      else begin : GEN_WIRE
         assign out_sig = in_sig;
      end
   endgenerate
endmodule
module deep_blocks (
   input  logic       clk,
   input  logic [3:0] val_in,
   output logic [3:0] val_out
);
   class dummy;
   endclass
   always_ff @(posedge clk) begin : L0
      begin : L1
         begin : L2
            val_out <= val_in;
         end
      end
   end
   always_ff @(posedge clk) begin
      automatic dummy d = new();
   end
endmodule
module const_fn_typedef (
   input  logic [7:0]  in_vec,
   output logic [15:0] out_vec
);
   typedef logic [15:0] word_t;
   function automatic word_t dup8(input logic [7:0] v);
      return {v, v};
   endfunction
   assign out_vec = dup8(in_vec);
endmodule
module assoc_array_case (
   input  logic          clk,
   input  logic [31:0]   key_in,
   input  logic [31:0]   val_in,
   output logic [31:0]   val_out
);
   int unsigned aa [int unsigned];
   always_ff @(posedge clk) begin
      aa[key_in] = val_in;
      unique0 case (key_in)
         0        : val_out <= aa[0];
         1,2,3    : val_out <= aa[key_in];
         default  : val_out <= aa.exists(key_in) ? aa[key_in] : '0;
      endcase
   end
endmodule
