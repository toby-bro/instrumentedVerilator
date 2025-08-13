module m_width_mismatch(input  logic [7:0] in,
                        output wire  [3:0] out);
    assign out = in;
endmodule
module m_latch_inference(input  logic sel,
                         output logic q);
    always @* begin
        if (sel) q = 1'b1;
    end
endmodule
module m_multidrive(input  logic a,
                    input  logic b,
                    output wire  y);
    wand w;
    assign w = a;
    assign w = b;
    assign y = w;
endmodule
module m_case_incomplete(input  logic [1:0] state,
                         output logic       next);
    always_comb begin
        unique case (state)
            2'b00: next = 1'b0;
            2'b01: next = 1'b1;
        endcase
    end
endmodule
module m_unused_signal(input  logic i,
                       output wire  o);
    logic unused_sig;
    assign o = i;
endmodule
module m_undriven_output(input  logic i,
                         output wire  o);
    wire dummy = i;
    assign o = i;
endmodule
module m_enum_uninit(input  logic clk,
                     output wire  y);
    typedef enum logic [1:0] {IDLE = 2'b00, RUN = 2'b01, STOP = 2'b10} state_t;
    state_t state;
    always_ff @(posedge clk) begin
        case (state)
            IDLE: state <= RUN;
            RUN:  state <= STOP;
            default: state <= IDLE;
        endcase
    end
    assign y = state[0];
endmodule
module m_packed_union(input  logic [3:0] in,
                      output logic [3:0] out);
    typedef union packed {
        logic [3:0]      a;
        logic [1:0][1:0] b;
    } u_t;
    u_t u;
    always_comb begin
        u.a = in;
        out = u.b[0];
    end
endmodule
module m_signed_unsigned(input  logic signed [3:0] a,
                         output wire        [3:0] y);
    assign y = a;
endmodule
module m_shift_large(input  logic [3:0] a,
                     output wire  [3:0] y);
    assign y = a << 5;
endmodule
module m_param_oob(input  logic [3:0] a,
                   output wire        y);
    parameter int IDX = 5;
    generate
        if (IDX < 4) begin : gen_in_range
            assign y = a[IDX];
        end else begin : gen_oob
            assign y = 1'b0;
        end
    endgenerate
endmodule
module m_logic_vs_wire(input  logic a,
                       output wire  y);
    wire  w;
    logic q;
    assign w = a;
    always_comb q = w;
    assign y = q;
endmodule
module m_tristate(input  logic a,
                  input  logic en,
                  output wire  y);
    assign y = en ? a : 1'bz;
endmodule
module m_array_bounds(input  logic [7:0] idx,
                      output wire        y);
    logic mem [0:3];
    assign y = mem[idx];
endmodule
module m_const_func(input  logic [3:0] a,
                    output wire  [3:0] y);
    function automatic logic [3:0] inc(input logic [3:0] x);
        inc = x + 1;
    endfunction
    assign y = inc(a);
endmodule
module m_packed_struct(input  logic [7:0] in,
                       output logic [7:0] out);
    typedef struct packed {
        logic [3:0] hi;
        logic [3:0] lo;
    } s_t;
    s_t s;
    always_comb begin
        s = '{hi: in[7:4], lo: in[3:0]};
        out = {s.hi, s.lo};
    end
endmodule
module m_concat_trunc(input  logic [7:0] a,
                      output wire  [15:0] y);
    assign y = {a, 1'b0};
endmodule
module m_width_ext(input  logic [15:0] in,
                   output wire   [7:0] out);
    assign out = {in, in} >> 3;
endmodule
module m_logic_unused_range(input  logic [3:0] in,
                            output wire        out);
    logic [7:0] wide = {4'h0, in};
    assign out = wide[7];
endmodule
module m_power_of_two_check(input  logic [3:0] in,
                            output wire        out);
    localparam int DIVISOR = 3;
    assign out = in / DIVISOR;
endmodule
