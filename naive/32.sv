module comb_adder #(
    parameter WIDTH = 8
) (
    input  logic [WIDTH-1:0] a,
    input  logic [WIDTH-1:0] b,
    output logic [WIDTH-1:0] sum
);
    always_comb begin
        sum = a + b;
    end
endmodule
module ff_counter (
    input  logic        clk,
    input  logic        rst_n,
    output logic [7:0]  count
);
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            count <= '0;
        else
            count <= count + 1'b1;
    end
endmodule
module param_mux #(
    parameter WIDTH = 8,
    parameter SEL   = 4
) (
    input  logic [WIDTH*SEL-1:0]                 data_flat,
    input  logic [$clog2(SEL)-1:0]               sel,
    output logic [WIDTH-1:0]                     y
);
    logic [WIDTH-1:0] data [0:SEL-1];
    integer idx;
    always_comb begin
        for (idx = 0; idx < SEL; idx++) begin
            data[idx] = data_flat[idx*WIDTH +: WIDTH];
        end
        y = data[sel];
    end
endmodule
module vector_reduction (
    input  logic [31:0] vec,
    output logic        parity
);
    assign parity = ^vec;
endmodule
module enum_state (
    input  logic clk,
    input  logic rst_n,
    input  logic in,
    output logic out
);
    typedef enum logic [1:0] { S0, S1, S2 } state_t;
    state_t state, next;
    always_comb begin
        case (state)
            S0:  next = in ? S1 : S0;
            S1:  next = in ? S2 : S0;
            S2:  next = in ? S2 : S1;
            default: next = S0;
        endcase
    end
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            state <= S0;
        else
            state <= next;
    end
    assign out = (state == S2);
endmodule
module struct_pack (
    input  logic [7:0]  in0,
    input  logic [7:0]  in1,
    output logic [15:0] combined
);
    typedef struct packed {
        logic [7:0] a;
        logic [7:0] b;
    } pair_t;
    pair_t p;
    always_comb begin
        p.a      = in0;
        p.b      = in1;
        combined = {p.a, p.b};
    end
endmodule
module union_example (
    input  logic [31:0] in,
    output logic [7:0]  byte0
);
    typedef union packed {
        logic [31:0]        word;
        logic [3:0][7:0]    bytes;
    } u_t;
    u_t u;
    always_comb begin
        u.word = in;
        byte0  = u.bytes[0];
    end
endmodule
module generate_array #(
    parameter N = 4
) (
    input  logic [N-1:0] in_vec,
    output logic [N-1:0] out_vec
);
    genvar i;
    generate
        for (i = 0; i < N; i++) begin : gen_block
            assign out_vec[i] = ~in_vec[i];
        end
    endgenerate
endmodule
module assert_check (
    input  logic clk,
    input  logic rst_n,
    input  logic cond,
    output logic pass
);
    always_ff @(posedge clk) begin
        if (!rst_n)
            pass <= 1'b0;
        else begin
            pass <= cond;
            assert (cond) else pass <= 1'b0;
        end
    end
endmodule
module class_demo (
    input  logic [7:0] in_value,
    output logic [7:0] out_value
);
    class incr_c;
        function new(); endfunction
        function automatic [7:0] do_inc(input [7:0] v);
            do_inc = v + 1'b1;
        endfunction
    endclass
    always_comb begin
        incr_c c = new();
        out_value = c.do_inc(in_value);
    end
endmodule
