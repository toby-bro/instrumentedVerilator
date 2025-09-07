module child_mod (
    input  logic [7:0] in,
    output logic [7:0] out
);
    assign out = in;
endmodule
module design_with_cells #(
    parameter int P_WIDTH = 8
) (
    input  logic                  clk,
    input  logic [P_WIDTH-1:0]    din,
    output logic [P_WIDTH-1:0]    dout
);
    logic [P_WIDTH-1:0] sig_a;
    logic [P_WIDTH-1:0] sig_array [0:3];
    typedef enum logic [1:0] {
        S_IDLE = 2'd0,
        S_RUN  = 2'd1,
        S_DONE = 2'd2
    } state_e;
    state_e current_state, next_state;
    typedef struct packed {
        logic [3:0] nibble0;
        logic [3:0] nibble1;
    } packed_data_t;
    typedef struct {
        logic [7:0] byte0;
        logic [7:0] byte1;
    } unpacked_data_t;
    packed_data_t   pkd;
    unpacked_data_t unpkd;
    typedef union packed {
        logic [7:0]        as_byte;
        packed_data_t      as_nibbles;
    } union_t;
    union_t u_data;
    localparam int CONST_VAL = 16;
    child_mod u_child (
        .in  (din),
        .out (dout)
    );
    function automatic logic [P_WIDTH-1:0] add_const(input logic [P_WIDTH-1:0] val);
        add_const = val + CONST_VAL;
    endfunction
    always_ff @(posedge clk) begin
        sig_a         <= add_const(din);
        current_state <= next_state;
        pkd.nibble0   <= din[3:0];
        pkd.nibble1   <= din[7:4];
        unpkd.byte0   <= din[7:0];
        unpkd.byte1   <= sig_a[7:0];
        u_data.as_byte <= din;
    end
endmodule
module class_holder (
    input  logic clk,
    input  logic rst,
    output logic [7:0] out
);
    class rng_gen;
        rand bit [7:0] value;
        function void gen();
            value = $urandom;
        endfunction
    endclass
    rng_gen gen_handle;
    always_ff @(posedge clk) begin
        if (rst) begin
            gen_handle = new();
        end
        if (gen_handle != null) begin
            gen_handle.gen();
            out <= gen_handle.value;
        end
        else begin
            out <= 8'h00;
        end
    end
endmodule
module packed_union_struct_test (
    input  logic [15:0] in_data,
    output logic [15:0] out_data
);
    typedef struct packed {
        logic [7:0] hi;
        logic [7:0] lo;
    } word_t;
    typedef union packed {
        word_t      w;
        logic [15:0] raw;
    } word_u;
    word_u data_u;
    always_comb begin
        data_u.raw = in_data;
        out_data   = {8'h00, data_u.w.hi} + {8'h00, data_u.w.lo};
    end
endmodule
module array_dimension_test #(
    parameter int DEPTH = 4
) (
    input  logic [7:0] d_in,
    output logic [7:0] d_out
);
    logic [7:0] mem [DEPTH];
    always_comb begin
        for (int i = 0; i < DEPTH; i++) begin
            mem[i] = d_in + i;
        end
        d_out = mem[0];
    end
endmodule
