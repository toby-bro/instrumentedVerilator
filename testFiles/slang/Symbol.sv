package types_pkg;
    typedef enum logic [1:0] {
        S_IDLE  = 2'd0,
        S_RUN   = 2'd1,
        S_STOP  = 2'd2
    } state_e;
    typedef struct packed {
        logic [3:0] a;
        logic [3:0] b;
    } packed_s;
    typedef struct {
        logic [7:0] c;
    } unpacked_s;
    typedef union packed {
        logic [7:0]      vec;
        packed_s         ps;
    } packed_u;
    typedef union {
        logic [15:0]     wide;
        unpacked_s       us;
    } unpacked_u;
    function automatic int add_int (input int lhs, input int rhs);
        return lhs + rhs;
    endfunction
endpackage
interface bus_if (input logic clk);
    logic [7:0] data;
    logic       ready;
    modport master  (output data, output ready);
    modport slave   (input  data,  input  ready);
endinterface
module simple_leaf #(
    parameter int WIDTH = 1
) (
    input  logic [WIDTH-1:0] a,
    output wire logic [WIDTH-1:0] y
);
    assign y = ~a;
endmodule
module generate_array (
    input  logic [7:0] din,
    output wire logic [7:0] dout
);
    genvar gi;
    generate
        for (gi = 0; gi < 8; gi++) begin : gbit
            simple_leaf #(.WIDTH(1)) u_leaf (
                .a (din[gi]),
                .y (dout[gi])
            );
        end
    endgenerate
endmodule
module type_param_mod #(
    type T = logic,
    parameter int DEPTH = 4
) (
    input  T din,
    output var T dout
);
    T mem [DEPTH];
    always_comb begin
        mem[0] = din;
        dout   = mem[0];
    end
endmodule
(* keep = "true", synthesis_keep = 1 *)
module attr_mod (
    input  logic a,
    output wire logic b
);
    (* preserve *) wire internal_sig;
    assign internal_sig = a;
    assign b            = internal_sig;
endmodule
module struct_mod (
    input  logic        clk,
    input  logic        rst,
    output wire logic [7:0] packed_union_vec
);
    import types_pkg::*;
    packed_s  ps;
    packed_u  pu;
    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            ps.a <= 4'h0;
            ps.b <= 4'h0;
        end
        else begin
            ps.a <= ps.a + 4'h1;
            ps.b <= ps.b + 4'h1;
        end
    end
    always_comb begin
        pu.ps = ps;
    end
    assign packed_union_vec = pu.vec;
endmodule
module if_user (
    input  logic  clk,
    input  logic  ext_in,
    output wire logic  ext_out,
    output wire logic [7:0] bus_data_o,
    output wire logic       bus_ready_o
);
    bus_if bus (.clk(clk));
    logic local_ready;
    assign bus.data   = {7'b0, ext_in};
    assign bus.ready  = local_ready;
    assign ext_out     = bus.data[0] & bus.ready;
    assign bus_data_o  = bus.data;
    assign bus_ready_o = bus.ready;
    always_comb begin
        local_ready = ext_in;
    end
endmodule
module primitive_mod (
    input  wire a,
    input  wire b,
    output wire y
);
    and u_and (y, a, b);
endmodule
module proc_mod (
    input  logic clk,
    input  logic rst,
    input  logic d,
    output logic q
);
    always_ff @(posedge clk or posedge rst) begin
        if (rst)
            q <= 1'b0;
        else
            q <= d;
    end
endmodule
