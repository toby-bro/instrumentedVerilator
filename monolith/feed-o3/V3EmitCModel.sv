module comb_and #(parameter WIDTH = 8)(
    input  logic [WIDTH-1:0] a_i,
    input  logic [WIDTH-1:0] b_i,
    output logic [WIDTH-1:0] y_o
);
    assign y_o = a_i & b_i;
endmodule
module seq_reg (
    input  logic clk_i,
    input  logic rst_i,
    input  logic d_i,
    output logic q_o
);
    always_ff @(posedge clk_i or posedge rst_i)
        if (rst_i)
            q_o <= 1'b0;
        else
            q_o <= d_i;
endmodule
module struct_union (
    input  logic [7:0] in_byte_i,
    output logic [7:0] out_byte_o
);
    typedef struct packed {
        logic [3:0] nibble_hi;
        logic [3:0] nibble_lo;
    } byte_struct_t;
    typedef union packed {
        byte_struct_t s;
        logic [7:0]   whole;
    } byte_union_t;
    byte_union_t u;
    always_comb begin
        u.whole = in_byte_i;
        out_byte_o = {u.s.nibble_lo, u.s.nibble_hi};
    end
endmodule
module enum_decoder (
    input  logic [1:0] sel_i,
    output logic [3:0] dec_o
);
    typedef enum logic [1:0] {
        SEL_0 = 2'b00,
        SEL_1 = 2'b01,
        SEL_2 = 2'b10,
        SEL_3 = 2'b11
    } sel_e;
    sel_e sel;
    always_comb begin
        sel = sel_e'(sel_i);
        dec_o = 4'b0000;
        case (sel)
            SEL_0: dec_o = 4'b0001;
            SEL_1: dec_o = 4'b0010;
            SEL_2: dec_o = 4'b0100;
            SEL_3: dec_o = 4'b1000;
            default: dec_o = 4'b0000;
        endcase
    end
endmodule
module gen_or #(parameter WIDTH = 32)(
    input  logic [WIDTH-1:0] vec_i,
    output logic             or_o
);
    logic [WIDTH-1:0] tmp;
    genvar i;
    generate
        for (i = 0; i < WIDTH; i++) begin : GEN_RED
            assign tmp[i] = vec_i[i];
        end
    endgenerate
    assign or_o = |tmp;
endmodule
module unpacked_array (
    input  logic [7:0] in_vec_i [0:3],
    output logic [7:0] out_vec_o [0:3]
);
    always_comb begin : ARRAY_COPY
        int idx;
        for (idx = 0; idx < 4; idx++) begin
            out_vec_o[idx] = in_vec_i[idx] + 8'd1;
        end
    end
endmodule
module class_proc (
    input  logic [31:0] a_i,
    input  logic [31:0] b_i,
    output logic [31:0] sum_o
);
    class adder_c;
        function automatic int add(int aa, int bb);
            return aa + bb;
        endfunction
    endclass
    always_comb begin
        automatic adder_c adder = new();
        sum_o = adder.add(a_i, b_i);
    end
endmodule
import "DPI-C" function int dpi_add(input int a, input int b);
module dpi_import (
    input  logic [31:0] in0_i,
    input  logic [31:0] in1_i,
    output logic [31:0] sum_o
);
    assign sum_o = dpi_add(in0_i, in1_i);
endmodule
module dpi_export (
    input  logic [15:0] a_i,
    input  logic [15:0] b_i,
    output logic [15:0] y_o
);
    function automatic int sv_mul(input int x, input int y);
        sv_mul = x * y;
    endfunction
    export "DPI-C" function sv_mul;
    assign y_o = sv_mul(a_i, b_i);
endmodule
module assert_example (
    input  logic       clk_i,
    input  logic       rst_n_i,
    input  logic [3:0] val_i,
    output logic [3:0] val_o
);
    assign val_o = val_i;
    always_ff @(posedge clk_i or negedge rst_n_i) begin
        if (!rst_n_i) begin
        end else begin
            assert (val_i !== 4'bxxxx);
        end
    end
endmodule
module simple_mem (
    input  logic        clk_i,
    input  logic        wr_en_i,
    input  logic [3:0]  addr_i,
    input  logic [7:0]  data_i,
    output logic [7:0]  data_o
);
    logic [7:0] mem [0:15];
    always_ff @(posedge clk_i) begin
        if (wr_en_i)
            mem[addr_i] <= data_i;
        data_o <= mem[addr_i];
    end
endmodule
module signed_unsigned (
    input  logic signed [7:0] s_in_i,
    input  logic        [7:0] u_in_i,
    output logic signed [8:0] diff_o
);
    assign diff_o = s_in_i - $signed(u_in_i);
endmodule
module nested_arrays (
    input  logic [1:0][3:0] in_mat_i,
    output logic [1:0][3:0] out_mat_o
);
    always_comb begin
        out_mat_o = in_mat_i;
    end
endmodule
module const_expr (
    input  logic       in_i,
    output logic [7:0] out_o
);
    localparam int CONST_A = 4;
    localparam int CONST_B = CONST_A * 2;
    assign out_o = {7'd0, (in_i ? CONST_B[0] : CONST_A[0])};
endmodule
module func_default_arg (
    input  logic [7:0]  in0_i,
    input  logic [7:0]  in1_i,
    output logic [15:0] out_o
);
    typedef struct packed {
        logic [15:0] val;
    } wide_t;
    function automatic wide_t make_wide(input logic [7:0] a, input logic [7:0] b = 8'hFF);
        make_wide.val = {a, b};
    endfunction
    always_comb begin
        automatic wide_t tmp;
        tmp = make_wide(in0_i, in1_i);
        out_o = tmp.val;
    end
endmodule
