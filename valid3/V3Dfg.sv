module slice_demo(
    input  logic [31:0] in_bus,
    output logic [7:0]  lower_byte,
    output logic [7:0]  upper_byte,
    output logic [15:0] middle_word
);
    assign lower_byte  = in_bus[7:0];
    assign upper_byte  = in_bus[31:24];
    assign middle_word = in_bus[23:8];
endmodule
module array_demo(
    input  logic [7:0] in_arr [0:3],
    output logic [9:0] sum_out
);
    integer i;
    logic [9:0] tmp_sum;
    always_comb begin
        tmp_sum = 10'd0;
        for (i = 0; i < 4; i++) begin
            tmp_sum = tmp_sum + in_arr[i];
        end
        sum_out = tmp_sum;
    end
endmodule
module const_demo(
    input  logic sel,
    output logic [127:0] const_val
);
    parameter logic [127:0] BIG_UNSIGNED = 128'hFF00_FF00_00FF_00FF_F0F0_0F0F_A5A5_5A5A;
    parameter        signed [63:0] BIG_SIGNED  = -64'sd123456789012345;
    assign const_val = sel ? BIG_UNSIGNED : {64'h0, BIG_SIGNED};
endmodule
module ternary_arith(
    input  logic [15:0] a,
    input  logic [15:0] b,
    input  logic        cond,
    output logic [15:0] result
);
    assign result = cond ? (a + b) : (a - b);
endmodule
module shift_rep(
    input  logic [7:0] datum,
    input  logic [2:0] shamt,
    output logic [31:0] out_shift_concat
);
    logic [7:0] shifted;
    assign shifted = datum << shamt;
    assign out_shift_concat = {4{shifted}};
endmodule
module concat_chain(
    input  logic [3:0] nibble0,
    input  logic [3:0] nibble1,
    input  logic [3:0] nibble2,
    input  logic [3:0] nibble3,
    output logic [15:0] word_out
);
    assign word_out = {nibble3, nibble2, nibble1, nibble0};
endmodule
module struct_demo(
    input  logic [7:0] in_byte,
    output logic [7:0] swapped
);
    typedef struct packed {
        logic [3:0] hi;
        logic [3:0] lo;
    } byte_parts_t;
    byte_parts_t bp_in, bp_out;
    always_comb begin
        bp_in = byte_parts_t'(in_byte);
        bp_out.hi = bp_in.lo;
        bp_out.lo = bp_in.hi;
        swapped   = bp_out;
    end
endmodule
module enum_demo(
    input  logic [1:0] sel,
    input  logic [7:0] value,
    output logic [7:0] out_val
);
    typedef enum logic [1:0] { IDLE = 2'd0, INC = 2'd1, DEC = 2'd2, INV = 2'd3 } op_t;
    op_t op;
    always_comb begin
        op = op_t'(sel);
        case (op)
            INC: out_val = value + 8'd1;
            DEC: out_val = value - 8'd1;
            INV: out_val = ~value;
            default: out_val = value;
        endcase
    end
endmodule
module fanout_demo(
    input  logic [7:0] in_sig,
    output logic [7:0] out1,
    output logic [7:0] out2,
    output logic [7:0] out3
);
    logic [7:0] temp;
    assign temp = in_sig ^ 8'hA5;
    assign out1 = temp;
    assign out2 = {~temp[3:0], temp[7:4]};
    assign out3 = temp & 8'h0F;
endmodule
module matrix_add(
    input  logic [7:0] matA [0:1][0:1],
    input  logic [7:0] matB [0:1][0:1],
    output logic [8:0] matC [0:1][0:1]
);
    integer i, j;
    always_comb begin
        for (i = 0; i < 2; i++) begin
            for (j = 0; j < 2; j++) begin
                matC[i][j] = matA[i][j] + matB[i][j];
            end
        end
    end
endmodule
