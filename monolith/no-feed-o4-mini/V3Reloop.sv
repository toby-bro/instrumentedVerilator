module createVarTemp_mod (
    input  logic [31:0] in0,
    input  logic [31:0] in1,
    output logic [31:0] out
);
    logic [31:0] __Vilp0;
    always_comb begin
        __Vilp0 = in0 ^ in1;
        out     = __Vilp0 + 1;
    end
endmodule
module mergeEnd_mod (
    input  logic [31:0] start,
    input  logic [31:0] step,
    input  logic [31:0] endp,
    output logic [31:0] items,
    output logic        done
);
    logic [31:0] indexLo;
    logic [31:0] indexHi;
    logic [31:0] _offset;
    always_comb begin
        indexLo = start;
        indexHi = endp;
        _offset = step;
        items   = indexHi - indexLo + 1;
        if (items >= _offset) begin
            done    = 1;
            indexLo = 0;
            indexHi = 0;
        end else begin
            done = 0;
        end
    end
endmodule
module visitNodeAssign_mod (
    input  logic        clk,
    input  logic        rst,
    input  logic [31:0] b0,
    input  logic [31:0] b1,
    input  logic [31:0] b2,
    input  logic [31:0] b3,
    input  logic [31:0] b4,
    input  logic [31:0] b5,
    input  logic [31:0] b6,
    output logic [31:0] a0,
    output logic [31:0] a1,
    output logic [31:0] a2,
    output logic [31:0] a3,
    output logic [31:0] a4
);
    always_ff @(posedge clk) begin
        if (rst) begin
            a0 <= '0;
            a1 <= '0;
            a2 <= '0;
            a3 <= '0;
            a4 <= '0;
        end else begin
            a0 <= b2;
            a1 <= b3;
            a2 <= b4;
            a3 <= b5;
            a4 <= b6;
        end
    end
endmodule
module visitNodeSel_mod (
    input  logic [7:0] in_vec,
    output logic [7:0] out_vec
);
    always_comb begin
        out_vec[3] = in_vec[5];
        out_vec[4] = in_vec[6];
        out_vec[5] = in_vec[7];
    end
endmodule
module visitNodeAssignLoop_mod (
    input  logic go,
    output logic done
);
    integer i;
    always_comb begin
        i    = 0;
        done = 0;
        while (i < 4) begin
            i = i + 1;
            if (i == 3)
                done = 1;
        end
    end
endmodule
module dynamic_assign_mod (
    input  logic [31:0] arr_in [0:7],
    input  logic  [2:0] idx,
    output logic [31:0] out_data
);
    always_comb begin
        out_data = arr_in[idx] + arr_in[idx + 1];
    end
endmodule
module complex_expr_mod (
    input  logic signed [15:0] a,
    input  logic signed [15:0] b,
    input  logic signed [15:0] c,
    input  logic signed [15:0] d,
    output logic signed [31:0] out
);
    always_comb begin
        out = (a + b) * (c - d);
    end
endmodule
module var_ref_mod (
    input  logic [15:0] a,
    input  logic [15:0] b,
    output logic [15:0] out
);
    logic [15:0] temp;
    always_comb begin
        temp = a & b;
        out  = temp;
    end
endmodule
module expr_stmt_mod (
    input  logic en,
    output logic y
);
    function logic foo(input logic x);
        return x ^ 1;
    endfunction
    always_comb begin
        if (en)
            y = foo(en);
        else
            y = 0;
    end
endmodule
module nested_block_mod (
    input  logic       ena,
    input  logic [7:0] in_data,
    output logic [7:0] out_data
);
    logic flag;
    always_comb begin
        out_data = 0;
        if (ena) begin
            begin
                flag = in_data[0];
                if (flag)
                    out_data = in_data << 1;
                else
                    out_data = in_data >> 1;
            end
        end
    end
endmodule
module const_assign_mod (
    input  logic [1:0] sel,
    output logic [7:0] out0,
    output logic [7:0] out1,
    output logic [7:0] out2
);
    always_comb begin
        out0 = 8'hFF;
        out1 = 8'hFF;
        out2 = 8'hFF;
        case (sel)
            2'd0: out0 = 8'hAA;
            2'd1: out1 = 8'hBB;
            2'd2: out2 = 8'hCC;
            default: begin end
        endcase
    end
endmodule
module reloopAll_mod (
    input  logic start,
    output logic done
);
    function logic subfunc(input logic x);
        return ~x;
    endfunction
    logic tmp;
    always_comb begin
        tmp  = subfunc(start);
        done = tmp;
    end
endmodule
