module mod_conditional (
    input  logic [7:0] in_val,
    output logic [7:0] out_val
);
    always_comb begin : UNIQUE_IF_EXAMPLE
        unique if (in_val == 8'd0)                     out_val = 8'h00;
        else if (in_val == 8'd1)                       out_val = 8'h11;
        else if (in_val inside {[8'd2:8'd10]})         out_val = 8'hAA;
        else                                           out_val = in_val;
    end
endmodule
module mod_case (
    input  logic [7:0] sel,
    output logic [7:0] decoded
);
    always_comb begin : UNIQUE_CASE_EXAMPLE
        unique case (sel)
            8'd0                   : decoded = 8'h00;
            8'd1, 8'd2, 8'd3       : decoded = 8'h0F;
            8'd4, 8'd5, 8'd6       : decoded = 8'hF0;
            default                : decoded = 8'hFF;
        endcase
    end
endmodule
module mod_case_inside (
    input  logic [7:0] sel,
    output logic       hit
);
    always_comb begin
        case (sel) inside
            [8'd0:8'd3] : hit = 1'b1;
            default     : hit = 1'b0;
        endcase
    end
endmodule
module mod_loops (
    input  logic        clk,
    input  logic [3:0]  loop_max,
    output logic [7:0]  loop_sum
);
    always_ff @(posedge clk) begin : VARIOUS_LOOPS
        integer i;
        integer j;
        integer k;
        loop_sum = 0;
        for (i = 0; i < loop_max; i++) begin
            loop_sum += i;
        end
        repeat (2) begin
            loop_sum += 8'h1;
        end
        j = loop_max;
        while (j > 0) begin
            loop_sum += j[7:0];
            j--;
        end
        k = 0;
        do begin
            k++;
        end while (k < 1);
        fork
            forever begin
                loop_sum = loop_sum;
            end
        join_any
        disable fork;
    end
endmodule
module mod_foreach (
    input  logic [31:0] packed_in,
    output logic [15:0] total
);
    logic [7:0] arr[0:3];
    always_comb begin : ARRAY_SPLIT
        arr[0] = packed_in[7 :0];
        arr[1] = packed_in[15:8];
        arr[2] = packed_in[23:16];
        arr[3] = packed_in[31:24];
    end
    always_comb begin : FOREACH_SUM
        total = 0;
        foreach (arr[idx]) begin
            total += arr[idx];
        end
    end
endmodule
module mod_proc_assign (
    input  logic        trig,
    input  logic [7:0]  data_in,
    output logic [7:0]  data_out
);
    logic temp_net;
    task automatic drive_net;
        assign   temp_net = trig;
        deassign temp_net;
    endtask
    always_comb begin
        drive_net();
        data_out = temp_net ? data_in : 8'h00;
    end
endmodule
module mod_block (
    input  logic        clk,
    input  logic [7:0]  a,
    input  logic [7:0]  b,
    output logic [7:0]  y
);
    always_ff @(posedge clk) begin : OUTER_BLOCK
        fork : PARALLEL_CALC
            begin : ADD_BLOCK
                y = a + b;
            end
            begin : SUB_BLOCK
                y = (a > b) ? (a - b) : (b - a);
            end
        join_none
        disable fork;
    end
endmodule
module mod_jump (
    input  logic [7:0] in_byte,
    output logic [7:0] out_byte
);
    function automatic void process_byte(input logic [7:0] v);
        integer idx;
        if (v == 8'h00) return;
        for (idx = 0; idx < 4; idx++) begin
            if (idx == 2) continue;
            if (idx == 3) break;
        end
    endfunction
    always_comb begin
        process_byte(in_byte);
        out_byte = in_byte;
    end
endmodule
module mod_assert (
    input  logic [7:0] din,
    output logic       ok
);
    always_comb begin
        assert (din !== 8'hFF) else ok = 1'b0;
        assume (din < 8'd250);
        cover  (din == 8'h00);
        ok = 1'b1;
    end
endmodule
module mod_event (
    input  logic en,
    output logic flag
);
    event ev;
    always_comb begin
        if (en) begin
            -> ev;
            flag = 1'b1;
        end
        else begin
            ->> ev;
            flag = 1'b0;
        end
    end
endmodule
module mod_disable_fork (
    input  logic clk,
    input  logic start,
    output logic done
);
    always_ff @(posedge clk) begin : DISABLE_EXAMPLE
        fork
            begin
                done = start;
            end
        join_any
        disable fork;
    end
endmodule
