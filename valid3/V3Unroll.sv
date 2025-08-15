module genvector_copy #(parameter int WIDTH = 8) (
    input  logic [WIDTH-1:0] in_bus,
    output logic [WIDTH-1:0] out_bus
);
    generate
        genvar gi;
        for (gi = 0; gi < WIDTH; gi = gi + 1) begin : gen_copy
            assign out_bus[gi] = in_bus[gi];
        end
    endgenerate
endmodule
module whilesum (
    input  logic [7:0] in_bus,
    output logic [3:0] ones_count
);
    always_comb begin
        int idx;
        ones_count = '0;
        idx = 0;
        while (idx < 8) begin
            ones_count = ones_count + in_bus[idx];
            idx = idx + 1;
        end
    end
endmodule
module nested_gen #(parameter int N = 4) (
    input  logic              in_sig,
    output logic [N-1:0]      replicated
);
    generate
        genvar x, y;
        for (x = 0; x < N; x = x + 1) begin : outer
            for (y = 0; y < 1; y = y + 1) begin : inner
                assign replicated[x] = in_sig;
            end
        end
    endgenerate
endmodule
module for_comb_negate #(parameter int W = 6) (
    input  logic [W-1:0] in_data,
    output logic [W-1:0] out_data
);
    integer j;
    always_comb begin
        for (j = 0; j < W; j = j + 1) begin
            out_data[j] = ~in_data[j];
        end
    end
endmodule
module named_begin_block (
    input  logic in_flag,
    output logic out_flag
);
    always_comb begin : outer_block
        begin : decision
            if (in_flag) begin : set_high
                out_flag = 1'b1;
            end else begin : set_low
                out_flag = 1'b0;
            end
        end
    end
endmodule
module while_external_inc (
    input  logic [3:0] in_vec,
    output logic [3:0] out_or
);
    always_comb begin
        int p;
        p = 0;
        out_or = '0;
        while (p < 4) begin
            out_or[p] = in_vec[p];
            p = p + 1;
        end
        p = p + 1;
    end
endmodule
module func_loop (
    input  logic [5:0] in_v,
    output logic [2:0] popcount
);
    function automatic [2:0] count_ones (input logic [5:0] val);
        int idx;
        count_ones = '0;
        for (idx = 0; idx < 6; idx = idx + 1) begin
            if (val[idx]) count_ones = count_ones + 1;
        end
    endfunction
    assign popcount = count_ones(in_v);
endmodule
