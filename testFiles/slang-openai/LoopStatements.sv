module for_loop_example (
    input  logic [15:0] in_bus,
    output logic [31:0] sum_out
);
    logic [7:0] mem [0:3];
    always_comb begin : proc_for
        int i;
        int j;
        for (i = 0; i < 4; i++) begin
            mem[i] = {4'b0, in_bus[i*4 +: 4]};
        end
        for (j = 3; j >= 0; j--) begin
            mem[j] = mem[j] ^ 8'hFF;
        end
    end
    assign sum_out = mem[0] + mem[1] + mem[2] + mem[3];
endmodule
module while_break_continue (
    input  logic        clk,
    input  logic [7:0]  sel,
    output logic [3:0]  idx_out
);
    logic [3:0] idx;
    always_ff @(posedge clk) begin : proc_while
        idx <= '0;
        while (idx < 8) begin
            idx <= idx + 1;
            if (sel[idx]) begin
                idx <= idx + 1;
                continue;
            end
            if (idx == 5)
                break;
        end
        idx_out <= idx;
    end
endmodule
module repeat_do_forever (
    input  logic       clk,
    input  logic [7:0] data_in,
    output logic [7:0] data_out
);
    logic [7:0] acc;
    always_ff @(posedge clk) begin : proc_loops
        int k;
        int m;
        int t;
        acc <= 0;
        k = 0;
        repeat (4) begin
            acc <= acc + data_in;
            k = k + 1;
        end
        m = 0;
        do begin
            m = m + 1;
        end while (m < 2);
        t = 0;
        forever begin
            data_out <= acc + m + t;
            t = t + 1;
            break;
        end
    end
endmodule
module foreach_example (
    input  logic [7:0] val_in,
    output logic [7:0] or_out
);
    logic [7:0] arr [0:1][0:3] = '{
        '{8'd0, 8'd1, 8'd2, 8'd3},
        '{8'd4, 8'd5, 8'd6, 8'd7}
    };
    always_comb begin : proc_foreach
        logic [7:0] tmp;
        tmp = 0;
        foreach (arr[a, j]) begin
            tmp |= arr[a][j] ^ val_in;
        end
        or_out = tmp;
    end
endmodule
module function_return_demo (
    input  logic [7:0] in_val,
    output logic [7:0] out_val
);
    function automatic logic [7:0] double_and_clip (input logic [7:0] v);
        logic [8:0] tmp;
        tmp = v * 2;
        if (tmp > 9'h0FF)
            return 8'hFF;
        else
            return tmp[7:0];
    endfunction
    always_comb begin : proc_call
        out_val = double_and_clip(in_val);
    end
endmodule
