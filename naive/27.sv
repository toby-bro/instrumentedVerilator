package common_pkg;
  typedef struct packed { logic [3:0] a; logic [3:0] b; } nibble_pair_t;
  typedef enum logic [1:0] { IDLE = 2'd0, RUN = 2'd1, DONE = 2'd2 } state_t;
  class math_c;
    int mult;
    function new(int unsigned a, int unsigned b);
      mult = a * b;
    endfunction
  endclass
endpackage
interface bus_if #(parameter WIDTH = 8) (input logic clk);
  logic [WIDTH-1:0] data;
  logic             valid;
  modport master (output data, valid);
  modport slave  (input  data, valid);
endinterface
module arithmetic_mod #(parameter WIDTH = 8) (
    input  logic clk,
    input  logic enable,
    input  logic [WIDTH-1:0] i_a,
    input  logic [WIDTH-1:0] i_b,
    output logic [(WIDTH*2)-1:0] o_mult
);
    import common_pkg::*;
    always_comb begin
        automatic math_c mc = new(i_a, i_b);
        o_mult = mc.mult;
    end
    property mult_check;
        @(posedge clk) disable iff (!enable) o_mult == i_a * i_b;
    endproperty
    assert property (mult_check);
endmodule
module state_machine_mod (
    input  logic clk,
    input  logic reset,
    input  logic start,
    output logic done
);
    import common_pkg::*;
    state_t cur, nxt;
    always_ff @(posedge clk or posedge reset) begin
        if (reset)
            cur <= IDLE;
        else
            cur <= nxt;
    end
    always_comb begin
        nxt  = cur;
        done = 1'b0;
        unique case (cur)
            IDLE: if (start) nxt = RUN;
            RUN : nxt = DONE;
            DONE: begin
                done = 1'b1;
                if (!start) nxt = IDLE;
            end
            default: nxt = IDLE;
        endcase
    end
endmodule
module bus_processor #(parameter WIDTH = 8) (
    input  logic                     clk,
    input  logic [WIDTH-1:0]         bus_data,
    input  logic                     bus_valid,
    output logic [WIDTH-1:0]         out_data
);
    always_comb begin
        if (bus_valid)
            out_data = bus_data;
        else
            out_data = '0;
    end
endmodule
module vector_sum #(parameter N = 4) (
    input  logic [N-1:0][7:0] vec_in,
    output logic [7:0]         sum
);
    wire [7:0] partial [N];
    genvar i;
    generate
        for (i = 0; i < N; i++) begin : gen_sum
            assign partial[i] = vec_in[i];
        end
    endgenerate
    integer j;
    always_comb begin
        sum = '0;
        for (j = 0; j < N; j++) begin
            sum = sum + partial[j];
        end
    end
endmodule
module union_packed_mod (
    input  logic [31:0] din,
    output logic [7:0]  byte0
);
    typedef union packed {
        logic [31:0]       word;
        logic [3:0][7:0]   bytes;
    } word_union_t;
    word_union_t u;
    always_comb begin
        u.word = din;
        byte0  = u.bytes[0];
    end
endmodule
module aa_lookup_mod (
    input  logic  [7:0]  key,
    output logic [15:0]  value
);
    typedef int unsigned uint_t;
    uint_t aa [byte];
    always_comb begin
        aa['h00] = 16'h1234;
        aa['hFF] = 16'hABCD;
        if (aa.exists(byte'(key)))
            value = aa[byte'(key)][15:0];
        else
            value = 16'h0000;
    end
endmodule
module queue_mod (
    input  logic        clk,
    input  logic        push,
    input  logic        pop,
    input  logic [7:0]  in_data,
    output logic [7:0]  out_data
);
    logic [7:0] q[$];
    always_ff @(posedge clk) begin
        if (push)
            q.push_back(in_data);
        if (pop && (q.size() > 0)) begin
            out_data <= q[0];
            q.pop_front();
        end
    end
endmodule
