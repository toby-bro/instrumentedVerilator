module inc_ff (
    input  logic        clk,
    input  logic [7:0]  in_val,
    output logic [7:0]  pre_out,
    output logic [7:0]  post_out
);
    logic [7:0] a;
    always_ff @(posedge clk) begin
        a        <= in_val;
        pre_out  <= ++a;
        post_out <= a++;
    end
endmodule
module arr_inc (
    input  logic [1:0]  idx_in,
    output logic [7:0]  data_out
);
    logic [7:0] arr [0:3];
    logic [1:0] idx;
    always_comb begin
        idx      = idx_in;
        data_out = arr[idx++];
    end
endmodule
module while_loop (
    input  logic        condition,
    input  logic [7:0]  in_val,
    output logic [7:0]  out_val
);
    logic [7:0] tmp;
    always_comb begin
        tmp = in_val;
        while (condition && tmp != 0) begin
            tmp = tmp - 1;
        end
        out_val = tmp;
    end
endmodule
module if_else_mod (
    input  logic        sel,
    input  logic [7:0]  x,
    input  logic [7:0]  y_in,
    output logic [7:0]  y_out
);
    always_comb begin
        if (sel)
            y_out = x + y_in;
        else
            y_out = x - y_in;
    end
endmodule
module case_mod (
    input  logic [1:0]  sel,
    input  logic [7:0]  x,
    output logic [7:0]  y
);
    always_comb begin
        case (sel)
            2'b00: y = x;
            2'b01: y = x + 1;
            2'b10: y = x - 1;
            default: begin
                y = x;
            end
        endcase
    end
endmodule
module wait_mod (
    input  logic        clk,
    input  logic [7:0]  in_val,
    output logic [7:0]  out_val
);
    logic [7:0] tmp;
    always_ff @(posedge clk) begin
        tmp      <= in_val;
        wait (tmp > 0);
        tmp      <= tmp - 1;
        out_val  <= tmp;
    end
endmodule
module foreach_mod #(
    parameter int N = 4
) (
    input  logic [7:0] arr_in [N],
    output logic [15:0] sum_out
);
    logic [15:0] sum;
    integer      i;
    always_comb begin
        sum = 0;
        foreach (arr_in[i]) begin
            sum = sum + arr_in[i];
        end
        sum_out = sum;
    end
endmodule
module gen_mod #(
    parameter int WIDTH = 8
) (
    input  logic        enable,
    output logic [WIDTH-1:0] out_vec
);
    genvar i;
    generate
        for (i = 0; i < WIDTH; i = i + 1) begin : gen_blk
            assign out_vec[i] = enable;
        end
    endgenerate
endmodule
module logic_expr (
    input  logic a,
    input  logic b,
    input  logic c,
    output logic y_and,
    output logic y_or,
    output logic y_eq
);
    always_comb begin
        y_and = a && b;
        y_or  = a || c;
        y_eq  = (b == c);
    end
endmodule
module cond_expr (
    input  logic [7:0] a,
    input  logic       sel,
    input  logic [7:0] b,
    input  logic [7:0] c,
    output logic [7:0] y
);
    assign y = sel ? b : c;
endmodule
module bit_select (
    input  logic [7:0] in_vec,
    input  logic       sel,
    output logic       bit_out,
    output logic       inv_bit
);
    always_comb begin
        bit_out = in_vec[sel];
        inv_bit = !in_vec[sel];
    end
endmodule
module concat_mod (
    input  logic [3:0] a,
    input  logic [3:0] b,
    output logic [7:0] c
);
    assign c = {a, b};
endmodule
