module begin_scope_mod(
    input  logic [7:0] in_data,
    output logic [7:0] out_data
);
    always_comb begin : outer_block
        int tmp;
        tmp = in_data;
        begin : inner_named
            int inner_tmp;
            inner_tmp = tmp;
            out_data  = inner_tmp;
        end
    end
endmodule
module foreach_array_mod(
    input  logic [7:0] in_data,
    output logic [15:0] sum_out
);
    logic [7:0] arr [0:3];
    always_comb begin
        int sum_local;
        sum_local = 0;
        arr[0] = in_data;
        arr[1] = in_data + 8'd1;
        arr[2] = in_data + 8'd2;
        arr[3] = in_data + 8'd3;
        foreach (arr[idx]) begin
            sum_local += arr[idx];
        end
        sum_out = sum_local;
    end
endmodule
module static_func_mod(
    input  logic        clk,
    input  logic [7:0]  val_in,
    output logic [7:0]  acc_out
);
    function automatic [7:0] accumulate(input logic [7:0] v);
        static int acc = 0;
        acc = acc + v;
        accumulate = acc[7:0];
    endfunction
    always_ff @(posedge clk) begin
        acc_out <= accumulate(val_in);
    end
endmodule
module typedef_mod(
    input  logic [7:0] data_in,
    output logic [7:0] data_out
);
    always_comb begin : typedef_block
        typedef struct packed {logic [3:0] nibble;} nib_t;
        nib_t s;
        s.nibble = data_in[3:0];
        data_out = {s.nibble, 4'h0};
    end
endmodule
module fork_mod(
    input  logic [7:0] a_in,
    output logic [7:0] a_out
);
    always @* begin : fork_block
        fork
            begin
                a_out = a_in;
            end
        join
    end
endmodule
module unique_if_mod(
    input  logic [1:0] sel,
    output logic [1:0] sel_out
);
    always_comb begin
        unique if (sel == 2'd0) sel_out = 2'd0;
        else if (sel == 2'd1) sel_out = 2'd1;
        else sel_out = 2'd2;
    end
endmodule
module foreach_string_mod(
    input  logic [7:0] idx_in,
    output byte char_out
);
    string str = "hello, verilator!";
    always_comb begin
        char_out = 8'd0;
        foreach (str[i]) begin
            if (i == idx_in) char_out = str[i];
        end
    end
endmodule
