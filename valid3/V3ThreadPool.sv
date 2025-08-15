module pool_ctor #(parameter WIDTH = 32, parameter GEN = 16)
                  (input  logic                    clk,
                   input  logic [WIDTH-1:0]        in_data,
                   output logic [WIDTH-1:0]        out_data);
    logic [WIDTH-1:0] stage [GEN-1:0];
    genvar i;
    generate
        for (i = 0; i < GEN; i++) begin : g_stage
            always_ff @(posedge clk)
                stage[i] <= (i == 0) ? in_data : stage[i-1] ^ {WIDTH{1'b1}};
        end
    endgenerate
    assign out_data = stage[GEN-1];
endmodule
module pool_dtor (input  logic        clk,
                  input  logic [15:0] din,
                  output logic [15:0] dout);
    typedef struct packed {
        logic [7:0] lo;
        logic [7:0] hi;
    } word_t;
    typedef union packed {
        word_t       w;
        logic [15:0] vec;
    } u_t;
    u_t transform;
    always_ff @(posedge clk) begin
        transform.vec  <= din;
        transform.w.hi <= transform.w.lo + 8'h1;
    end
    assign dout = transform.vec;
endmodule
module pool_enqueue (input  logic        clk,
                     input  logic [7:0]  key_in,
                     output logic [15:0] value_out);
    logic [15:0] queue_data [$];
    logic [15:0] assoc_data [byte];
    always_ff @(posedge clk) begin
        queue_data.push_front({8'hAA, key_in});
        assoc_data[key_in] <= queue_data.pop_back();
    end
    assign value_out = assoc_data[key_in];
endmodule
module pool_wait (input  logic       clk,
                  input  logic       valid_i,
                  input  logic [7:0] data_i,
                  output logic [7:0] data_o);
    always_ff @(posedge clk) begin
        if (valid_i) data_o <= data_i;
    end
    property p_transfer;
        @(posedge clk) valid_i |-> (data_o == data_i);
    endproperty
    assert property (p_transfer);
    cover property (@(posedge clk) valid_i);
endmodule
module pool_start_worker (input  logic       clk,
                          input  logic [1:0] cmd,
                          output logic [3:0] status);
    typedef enum logic [1:0] {IDLE, BUSY, DONE, ERR} state_t;
    state_t state;
    always_ff @(posedge clk) begin
        unique case (cmd)
            2'd0: state <= IDLE;
            2'd1: state <= BUSY;
            2'd2: state <= DONE;
            default: state <= ERR;
        endcase
    end
    assign status = {2'b00, state};
endmodule
module pool_worker_loop (input  logic        clk,
                         input  logic [31:0] seed,
                         output logic [31:0] rnd_out);
    class prng;
        rand logic [31:0] value;
        function new(logic [31:0] s); value = s; endfunction
        function logic [31:0] next();
            value = {value[30:0], value[31] ^ value[21] ^ value[1] ^ value[0]};
            return value;
        endfunction
    endclass
    prng p;
    initial p = new(32'h1);
    always_ff @(posedge clk)
        rnd_out <= p.next() ^ seed;
endmodule
module pool_lambda (input  logic [15:0] in_a,
                    input  logic [15:0] in_b,
                    output logic [15:0] out_sum);
    function automatic logic [15:0] add16(input logic [15:0] a, input logic [15:0] b);
        add16 = a + b;
    endfunction
    assign out_sum = add16(in_a, in_b);
endmodule
module pool_mt_disabled (input  logic [7:0] in_val,
                         output logic [7:0] out_val);
    function automatic logic [7:0] mirror(input logic [7:0] v);
        mirror = {<<{v}};
    endfunction
    assign out_val = mirror(in_val);
    always_comb begin
        assert(out_val == mirror(in_val));
    end
endmodule
module pool_selftest #(parameter DEPTH = 4)
                      (input  logic                     clk,
                       input  logic [DEPTH-1:0]         vec_in,
                       output logic [DEPTH-1:0]         vec_out);
    localparam int SIZE = 1 << DEPTH;
    logic [DEPTH-1:0] mem [SIZE-1:0];
    genvar i;
    generate
        for (i = 0; i < SIZE; i++) begin : g_mem
            always_ff @(posedge clk)
                mem[i] <= vec_in ^ i[DEPTH-1:0];
        end
    endgenerate
    assign vec_out = mem[SIZE-1];
endmodule
module pool_lambda1 (input  logic [31:0] in_data,
                     output logic [31:0] out_data);
    typedef struct packed {
        logic [15:0] lo;
        logic [15:0] hi;
    } parts_t;
    parts_t p;
    always_comb begin
        p = '{lo: in_data[15:0], hi: in_data[31:16]};
        out_data = {p.hi, p.lo};
    end
endmodule
module pool_lambda2 (input  logic       clk,
                     input  logic [7:0] idx,
                     output logic [7:0] data_o);
    logic [7:0] dyn_array [];
    initial begin
        dyn_array = new[16];
        foreach (dyn_array[i]) dyn_array[i] = i;
    end
    always_ff @(posedge clk)
        data_o <= (idx < dyn_array.size()) ? dyn_array[idx] : 8'hFF;
endmodule
module pool_lambda3 (input  logic       clk,
                     input  logic [7:0] push_val,
                     input  logic       push_en,
                     output logic [7:0] front_val);
`ifdef USE_QUEUE
    logic [7:0] q [$];
    always_ff @(posedge clk) begin
        if (push_en) q.push_front(push_val);
    end
    assign front_val = (q.size() != 0) ? q[0] : 8'h00;
`else
    assign front_val = push_val;
`endif
endmodule
module scope_ctor #(parameter WIDTH = 8)
                   (input  logic                 clk,
                    input  logic [WIDTH-1:0]     din,
                    output logic [WIDTH-1:0]     dout);
    typedef logic [WIDTH-1:0] word_t;
    word_t internal;
    always_ff @(posedge clk)
        internal <= din + 1;
    assign dout = internal;
endmodule
module scope_enqueue (input  logic       clk,
                      input  logic [3:0] sig_in,
                      output logic [3:0] sig_out);
    always_ff @(posedge clk)
        sig_out <= sig_in;
endmodule
interface simple_if #(parameter W = 4) ();
    logic [W-1:0] data;
    modport slave (input data);
endinterface
module scope_wait (input  logic       clk,
                   input  logic [3:0] d_in,
                   output logic [3:0] d_out);
    simple_if #(4) sif();
    always_ff @(posedge clk)
        sif.data <= d_in;
    assign d_out = sif.data;
endmodule
