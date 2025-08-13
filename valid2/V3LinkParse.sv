module m_typedef_public_enum
    #(parameter int WIDTH = 8)
    (input  logic               clk,
     input  logic [WIDTH-1:0]   din,
     output logic [WIDTH-1:0]   dout);
    timeunit 1ns/1ns;
    (* verilator, public *)
    typedef enum logic [1:0] {
        S_IDLE  = 2'd0,
        S_RUN   = 2'd1,
        S_DONE  = 2'd2,
        S_ERR   = 2'd3
    } state_t;
    (* verilator, public_flat_rw *)
    state_t state_var = S_IDLE;
    always_ff @(posedge clk) begin
        state_var <= (state_var == S_IDLE) ? S_RUN : S_IDLE;
    end
    assign dout = (state_var == S_RUN) ? din : {WIDTH{1'b0}};
endmodule
module m_var_split_forceable
    (input  logic clk,
     input  logic rst_n,
     output logic active);
    timeunit 1ns/1ns;
    (* verilator, split_var, forceable *)
    enum logic {IDLE, BUSY} status = IDLE;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            status <= IDLE;
        else
            status <= (status == IDLE) ? BUSY : IDLE;
    end
    assign active = (status == BUSY);
endmodule
module m_clocking_default_skew
    (input  logic clk,
     input  logic d,
     output logic q);
    timeunit 1ns/1ns;
    clocking cb @(posedge clk);
        default input  #1step;
        default output #0;
        input  d;
        output q;
    endclocking
    always_ff @(cb) begin
        cb.q <= cb.d;
    end
endmodule
module m_generate_unnamed
    (input  logic clk,
     input  logic [3:0] in_vec,
     output logic [3:0] out_vec);
    timeunit 1ns/1ns;
    genvar i;
    for (i = 0; i < 4; i++) begin : gen_loop
        if (i[0]) begin : blk1
            logic tmp;
            always_ff @(posedge clk) tmp <= in_vec[i];
            assign out_vec[i] = tmp;
        end
        else begin : blk2
            assign out_vec[i] = in_vec[i];
        end
    end
endmodule
module m_foreach
    (input  logic             clk,
     input  logic [7:0]       data_in,
     output logic [31:0]      sum_out);
    timeunit 1ns/1ns;
    logic [7:0] mem [0:3];
    int         sum;
    always_ff @(posedge clk) begin
        mem[0] <= data_in;
        mem[1] <= mem[0];
        mem[2] <= mem[1];
        mem[3] <= mem[2];
    end
    always_comb begin
        sum = 0;
        foreach (mem[idx]) begin
            sum += mem[idx];
        end
    end
    assign sum_out = sum;
endmodule
module m_wait_zero
    (input  logic clk,
     input  logic in_sig,
     output logic out_sig);
    timeunit 1ns/1ns;
    always_ff @(posedge clk) begin
        wait (0);
        out_sig <= in_sig;
    end
endmodule
module m_function_lifetime
    (input  logic [7:0] a,
     output logic [7:0] y);
    timeunit 1ns/1ns;
    function automatic logic [7:0] f(input logic [7:0] x);
        static int cnt = 0;
        cnt = cnt + 1;
        f = x + cnt[7:0];
    endfunction
    assign y = f(a);
endmodule
module m_cover
    (input  logic clk,
     input  logic trig,
     output logic pass);
    timeunit 1ns/1ns;
    property p_always_high; @(posedge clk) trig; endproperty
    cover property (p_always_high);
    assign pass = trig;
endmodule
module m_unsized_const
    (input  logic             in_bit,
     output logic [3:0]       out_vec);
    timeunit 1ns/1ns;
    logic [3:0] local_vec = '0;
    assign out_vec = local_vec | {3'b000, in_bit};
endmodule
