module sa_basic (
    input  logic clk,
    input  logic i_data,
    output logic o_data
);
    (* isolate_assignments *) logic x;
    logic y;
    always_ff @(posedge clk) begin
        x <= i_data;
        y <= x;
        x <= y ^ i_data;
    end
    assign o_data = x ^ y;
endmodule
module sa_nested (
    input  logic       clk,
    input  logic [3:0] a,
    output logic [3:0] b
);
    (* isolate_assignments *) logic [3:0] s;
    logic [3:0] r;
    always_ff @(posedge clk) begin
        if (a[0]) begin
            s <= a;
            if (a[1]) begin
                r <= s + a;
            end else begin
                s <= a + 1;
            end
        end else begin
            r <= s;
        end
    end
    assign b = r ^ s;
endmodule
module sa_function (
    input  logic       clk,
    input  logic [7:0] din,
    output logic [7:0] dout
);
    function automatic logic [7:0] swapbits (input logic [7:0] v);
        swapbits = {v[3:0], v[7:4]};
    endfunction
    (* isolate_assignments *) logic [7:0] reg1;
    logic [7:0] reg2;
    always_ff @(posedge clk) begin
        reg1 <= swapbits(din);
        reg2 <= reg1 ^ din;
    end
    assign dout = reg2;
endmodule
module sa_array (
    input  logic       clk,
    input  logic [1:0] sel,
    input  logic [7:0] din,
    output logic [7:0] dout
);
    (* isolate_assignments *) logic [7:0] mem [0:3];
    logic [7:0] tmp;
    always_ff @(posedge clk) begin
        mem[sel] <= din;
        tmp      <= mem[sel] + din;
    end
    assign dout = tmp;
endmodule
module sa_comb (
    input  logic [7:0] a,
    output logic [7:0] b
);
    (* isolate_assignments *) logic [7:0] comb_reg;
    logic [7:0] other;
    always_comb begin
        comb_reg = a;
        other    = comb_reg + 8'd1;
    end
    assign b = other;
endmodule
module sa_case (
    input  logic       clk,
    input  logic [1:0] sel,
    output logic [3:0] y
);
    (* isolate_assignments *) logic [3:0] state;
    logic [3:0] next_val;
    always_ff @(posedge clk) begin
        case (sel)
            2'b00: state <= 4'd0;
            2'b01: state <= 4'd1;
            2'b10: begin
                state   <= 4'd2;
                next_val <= state;
            end
            default: state <= state + 1'b1;
        endcase
    end
    assign y = next_val;
endmodule
module sa_for (
    input  logic clk,
    input  logic start,
    output logic [7:0] sum_out
);
    (* isolate_assignments *) logic [7:0] acc;
    int i;
    logic [7:0] sum;
    always_ff @(posedge clk) begin
        if (start) begin
            acc <= 8'd0;
            for (i = 0; i < 4; i++) begin
                acc <= acc + i[7:0];
            end
            sum <= acc;
        end
    end
    assign sum_out = sum;
endmodule
module sa_generate #(
    parameter int N = 4
) (
    input  logic               clk,
    input  logic [N-1:0]       a,
    output logic [N-1:0]       b
);
    (* isolate_assignments *) logic [N-1:0] regs [0:N-1];
    logic [N-1:0] merge;
    genvar g;
    generate
        for (g = 0; g < N; g++) begin : genblk
            always_ff @(posedge clk) begin
                regs[g] <= {N{a[g]}};
            end
        end
    endgenerate
    always_comb begin
        merge = '0;
        for (int k = 0; k < N; k++) begin
            merge = merge ^ regs[k];
        end
    end
    assign b = merge;
endmodule
