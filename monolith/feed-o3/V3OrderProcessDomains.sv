module seq_combo_hybrid (
    input  logic        clk,
    input  logic        reset_n,
    input  logic [7:0]  data_in,
    output logic [7:0]  data_out
);
    logic [7:0] state_reg;
    logic [7:0] next_state;
    logic [7:0] hybrid_reg;
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n)
            state_reg <= 8'h00;
        else
            state_reg <= next_state;
    end
    always_comb begin
        next_state = state_reg + data_in;
    end
    always @(posedge clk or data_in) begin
        hybrid_reg <= state_reg ^ data_in;
    end
    assign data_out = hybrid_reg;
endmodule
module multi_clock_domain (
    input  logic clk_a,
    input  logic clk_b,
    input  logic sel,
    input  logic din,
    output logic dout
);
    logic reg_a;
    logic reg_b;
    always_ff @(posedge clk_a) begin
        reg_a <= din;
    end
    always_ff @(posedge clk_b) begin
        reg_b <= reg_a;
    end
    assign dout = sel ? reg_b : reg_a;
endmodule
module hybrid_async_reset (
    input  logic clk,
    input  logic async_sig,
    input  logic in_a,
    output logic out_b
);
    logic latch_q;
    always @(posedge clk or posedge async_sig) begin
        if (async_sig)
            latch_q <= 1'b0;
        else
            latch_q <= in_a;
    end
    assign out_b = latch_q;
endmodule
module latch_module (
    input  logic        en,
    input  logic [3:0]  din,
    output logic [3:0]  q
);
    always_latch begin
        if (en)
            q <= din;
    end
endmodule
module func_module (
    input  logic [15:0] in1,
    input  logic [15:0] in2,
    output logic [15:0] out1
);
    function automatic [15:0] add_func (input [15:0] a, input [15:0] b);
        add_func = a + b;
    endfunction
    assign out1 = add_func(in1, in2);
endmodule
module gen_module #(
    parameter int WIDTH = 4
) (
    input  logic                   clk,
    input  logic                   reset,
    input  logic [WIDTH-1:0]       din,
    output logic [WIDTH-1:0]       dout
);
    typedef struct packed {
        logic val;
    } bitwrap_t;
    bitwrap_t registers [WIDTH];
    genvar i;
    generate
        for (i = 0; i < WIDTH; i++) begin : gen_blk
            always_ff @(posedge clk or posedge reset) begin
                if (reset)
                    registers[i].val <= 1'b0;
                else
                    registers[i].val <= din[i];
            end
        end
    endgenerate
    always_comb begin
        for (int j = 0; j < WIDTH; j++) begin
            dout[j] = registers[j].val;
        end
    end
endmodule
module unique_case_module (
    input  logic [1:0] sel,
    input  logic       in_signal,
    output logic       out_signal
);
    always_comb begin
        unique case (sel)
            2'b00   : out_signal = 1'b0;
            2'b01   : out_signal = in_signal;
            2'b10   : out_signal = ~in_signal;
            default : out_signal = 1'bx;
        endcase
    end
endmodule
module dead_logic (
    input  logic in_sig,
    output logic out_sig
);
    logic [3:0] unused;
    always_comb begin
        unused = 4'hA;
    end
    assign out_sig = in_sig;
endmodule
