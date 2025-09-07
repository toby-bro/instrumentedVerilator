module split_nested_if
    (input  logic         clk,
     input  logic         rst_n,
     input  logic  [7:0]  in_a,
     input  logic  [7:0]  in_b,
     output logic  [7:0]  a_out,
     output logic  [7:0]  b_out);
    logic [7:0] a;
    logic [7:0] b;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            a <= '0;
            b <= '0;
        end else begin
            if (in_a[0]) begin
                a <= in_a;
                b <= in_b;
            end else begin
                if (in_b[0]) begin
                    a <= a + 1;
                    b <= b + 2;
                end else begin
                    a <= a - 1;
                    b <= b - 2;
                end
            end
        end
    end
    assign a_out = a;
    assign b_out = b;
endmodule
module reorder_chain
    (input  logic        clk,
     input  logic        rst,
     input  logic [7:0]  v0,
     output logic [7:0]  v3);
    logic [7:0] v1;
    logic [7:0] v2;
    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            v1 <= '0;
            v2 <= '0;
            v3 <= '0;
        end else begin
            v1 <= 8'h00;
            v1 <= v0;
            if (v0[0]) begin
                v2 <= v1;
                v3 <= v2;
            end else begin
                v2 <= v1 + 1;
                v3 <= v2 + 1;
            end
        end
    end
endmodule
module mix_block_nb
    (input  logic       clk,
     input  logic [3:0] data_in,
     output logic [3:0] data_out);
    logic [3:0] reg_a;
    logic [3:0] reg_b;
    always_ff @(posedge clk) begin
        reg_a <= data_in;
    end
    always_ff @(posedge clk) begin
        reg_b <= reg_a;
    end
    assign data_out = reg_b;
endmodule
module logic_comb
    (input  logic [15:0] x,
     input  logic [15:0] y,
     output logic [15:0] z);
    always_comb begin
        if (x > y) begin
            z = x - y;
        end else begin
            z = x + y;
        end
    end
endmodule
module for_loop_usage
    (input  logic [1:0]           sel,
     input  logic [7:0]           vec_in [0:3],
     output logic [7:0]           sel_out);
    int i;
    always_comb begin
        sel_out = '0;
        for (i = 0; i < 4; i++) begin
            if (sel == i[1:0]) sel_out = vec_in[i];
        end
    end
endmodule
module case_statements
    (input  logic [1:0] state_in,
     output logic [3:0] led_out);
    always_comb begin
        case (state_in)
            2'b00:   led_out = 4'h1;
            2'b01:   led_out = 4'h3;
            2'b10:   led_out = 4'h7;
            default: led_out = 4'hF;
        endcase
    end
endmodule
module function_usage
    (input  logic [7:0] a,
     input  logic [7:0] b,
     output logic [7:0] gcd_out);
    function automatic [7:0] gcd (input logic [7:0] x_in, input logic [7:0] y_in);
        logic [7:0] x;
        logic [7:0] y;
        logic [7:0] temp;
        begin
            x = x_in;
            y = y_in;
            while (y != 0) begin
                temp = y;
                y    = x % y;
                x    = temp;
            end
            gcd = x;
        end
    endfunction
    assign gcd_out = gcd(a, b);
endmodule
