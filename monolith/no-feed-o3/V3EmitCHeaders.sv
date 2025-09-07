module leaf #(
    parameter WIDTH = 8
) (
    input  logic [WIDTH-1:0] a,
    output logic [WIDTH-1:0] y
);
    assign y = a;
endmodule
module packed_struct_mod (
    input  logic        clk,
    input  logic [15:0] din,
    output logic [15:0] dout
);
    typedef enum logic [1:0] {
        PS_IDLE = 2'b00,
        PS_RUN  = 2'b01,
        PS_DONE = 2'b10
    } ps_state_e;
    typedef struct packed {
        logic [3:0] lo;
        logic [3:0] hi;
    } nibble_t;
    typedef union packed {
        logic  [15:0]         word;
        logic  [7:0]          byte [2];
        nibble_t              nibbles [2];
    } word_view_u;
    typedef struct packed {
        word_view_u           view;
        logic [15:0]          parity;
    } complex_packed_t;
    complex_packed_t        cpx_reg;
    always_ff @(posedge clk) begin
        cpx_reg.view.word <= din;
        cpx_reg.parity    <= din ^ 16'hFFFF;
        dout              <= cpx_reg.view.word ^ cpx_reg.parity;
    end
endmodule
module unpacked_struct_mod #(
    parameter int WIDTH_A = 8,
    parameter int WIDTH_B = 8
) (
    input  logic                 clk,
    input  logic                 en,
    input  logic [WIDTH_A-1:0]   a_in,
    input  logic [WIDTH_B-1:0]   b_in,
    output logic [WIDTH_A+WIDTH_B-1:0] sum_out
);
    typedef struct {
        logic [WIDTH_A-1:0] a;
        logic [WIDTH_B-1:0] b;
    } pair_s;
    typedef struct {
        pair_s               p0;
        pair_s               p1;
    } double_pair_s;
    double_pair_s            dp_reg;
    always_ff @(posedge clk) begin
        if (en) begin
            dp_reg.p0.a <= a_in;
            dp_reg.p0.b <= b_in;
            dp_reg.p1   <= dp_reg.p0;
            sum_out     <= dp_reg.p1.a + dp_reg.p1.b;
        end
    end
endmodule
module param_module #(
    parameter int SIZE = 4
) (
    input  logic [SIZE-1:0]  in_data,
    output logic [SIZE-1:0]  out_data
);
    parameter logic [7:0]  P8  = 8'hA5;
    localparam int         LPW = 32;
    typedef enum logic [1:0] {
        P_IDLE  = 2'd0,
        P_BUSY  = 2'd1,
        P_ERROR = 2'd2
    } pm_state_e;
    assign out_data = in_data ^ P8[SIZE-1:0];
endmodule
module with_cell_mod (
    input  logic [7:0] in_bus,
    output logic [7:0] out_bus
);
    leaf #(.WIDTH(8)) u_leaf (
        .a (in_bus),
        .y (out_bus)
    );
endmodule
