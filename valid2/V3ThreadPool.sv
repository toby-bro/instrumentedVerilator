`timescale 1ns/1ps
module tp_constructor_mod #(parameter int N = 128)
    (input  logic               clk,
     input  logic [31:0]        din,
     output logic [31:0]        dout);
    genvar i;
    logic [31:0] sum [0:N-1];
    generate
        for (i = 0; i < N; i++) begin : GEN_SUM
            assign sum[i] = din + i;
        end
    endgenerate
    always_ff @(posedge clk) begin
        dout <= sum[din % N];
    end
endmodule
module tp_destructor_mod
    (input  logic               clk,
     input  logic [31:0]        din,
     output logic [31:0]        dout);
    logic [31:0] shift [0:15];
    always_ff @(posedge clk) begin
        shift[0] <= din;
        for (int j = 1; j < 16; j++) begin
            shift[j] <= shift[j-1];
        end
        dout <= shift[15];
    end
endmodule
module tp_enqueue_mod
    (input  logic               clk,
     input  logic [31:0]        din,
     output logic [31:0]        dout);
    int q[$];
    always_ff @(posedge clk) begin
        q.push_back(din);
        if (q.size() > 8) q.pop_front();
        if (q.size() != 0) dout <= q[$-1];
        else               dout <= 32'd0;
    end
endmodule
module tp_wait_mod
    (input  logic clk,
     input  logic trig,
     output logic ready);
    event ev;
    always_ff @(posedge clk) begin
        if (trig) -> ev;
    end
    always @(ev) begin
        ready = 1'b1;
    end
endmodule
module tp_startWorker_mod
    (input  logic        clk,
     input  logic [7:0]  din,
     output logic [7:0]  dout);
    class Worker;
        rand bit [7:0] val;
        function void doWork(input bit [7:0] base);
            val = base + 8'h1;
        endfunction
    endclass
    Worker w;
    always_ff @(posedge clk) begin
        w = new();
        w.doWork(din);
        dout <= w.val;
    end
endmodule
module tp_workerJobLoop_mod
    (input  logic               clk,
     input  logic [31:0]        din,
     output logic [31:0]        dout);
    int arr [0:9];
    always_ff @(posedge clk) begin
        foreach (arr[i]) arr[i] = din + i;
        dout <= arr[din % 10];
    end
endmodule
module tp_workerJobLoopLambda_mod
    (input  logic               clk,
     input  logic [31:0]        din,
     output logic [31:0]        dout);
    function automatic logic [31:0] calc (input logic [31:0] a);
        calc = a * a;
    endfunction
    always_ff @(posedge clk) begin
        dout <= calc(din);
    end
endmodule
module tp_selfTestDisabled_mod
    (input  logic       clk,
     input  logic [3:0] in,
     output logic       out);
    typedef enum logic [1:0] {S0, S1, S2, S3} state_t;
    state_t state;
    always_ff @(posedge clk) begin
        unique case (in)
            4'h0: state <= S0;
            4'h1: state <= S1;
            4'h2: state <= S2;
            default: state <= S3;
        endcase
        out <= (state == S2);
    end
endmodule
module tp_selfTest_mod
    (input  logic               clk,
     input  logic [15:0]        in,
     output logic [15:0]        out);
    typedef struct packed {logic [7:0] a; logic [7:0] b;} pair_t;
    pair_t p;
    always_comb begin
        p.a = in[7:0];
        p.b = in[15:8];
    end
    always_ff @(posedge clk) begin
        out <= {8'd0, p.a} + {8'd0, p.b};
    end
endmodule
module tp_selfTestLambdaA_mod
    (input  logic       clk,
     input  logic [7:0] din,
     output logic [7:0] dout);
    function automatic [7:0] f(input [7:0] x);
        f = x + 8'd10;
    endfunction
    always_ff @(posedge clk) begin
        dout <= f(din);
    end
endmodule
module tp_selfTestLambdaB_mod
    (input  logic       clk,
     input  logic [7:0] din,
     output logic [7:0] dout);
    function automatic [7:0] g(input [7:0] x);
        g = x << 1;
    endfunction
    always_ff @(posedge clk) begin
        dout <= g(din);
    end
endmodule
module tp_selfTestLambdaC_mod
    (input  logic       clk,
     input  logic [7:0] din,
     output logic [7:0] dout);
    function automatic [7:0] h(input [7:0] x);
        h = x ^ 8'hFF;
    endfunction
    always_ff @(posedge clk) begin
        dout <= h(din);
    end
endmodule
module tp_scopeConstructor_mod
    (input  logic clk,
     input  logic valid,
     output logic ready);
    bit flag;
    always_ff @(posedge clk) begin
        flag  <= valid;
        ready <= flag;
    end
endmodule
module tp_scopeEnqueue_mod
    (input  logic       clk,
     input  logic [7:0] din,
     output logic [7:0] dout);
    bit [7:0] q[$];
    always_ff @(posedge clk) begin
        q.push_back(din);
        if (q.size() > 0) dout <= q.pop_front();
    end
endmodule
module tp_scopeWait_mod
    (input  logic clk,
     input  logic start,
     output logic done);
    int counter;
    always_ff @(posedge clk) begin
        if (start)              counter <= 4;
        else if (counter != 0)  counter <= counter - 1;
        done <= (counter == 0);
    end
endmodule
