interface simple_if #(parameter WIDTH = 8) ();
    logic [WIDTH-1:0] data;
    logic             en;
endinterface
module param_adder #(parameter WIDTH = 8) (
    input  logic [WIDTH-1:0] in,
    output logic [WIDTH-1:0] out
);
    assign out = in + {WIDTH{1'b1}};
endmodule
module struct_union_example (
    input  logic [31:0] in,
    output logic [31:0] out
);
    typedef struct packed {
        logic [7:0]  a;
        logic [7:0]  b;
        logic [15:0] c;
    } my_s;
    typedef union packed {
        my_s         s;
        logic [31:0] word;
    } my_u;
    my_u u;
    always_comb begin
        u.word = in;
        out    = {u.s.a, u.s.b, u.s.c};
    end
endmodule
module class_usage (
    input  logic        clk,
    input  logic [7:0]  din,
    output logic [7:0]  dout
);
    class my_c;
        rand bit [7:0] data;
        function automatic bit [7:0] incr();
            return data + 1;
        endfunction
    endclass
    my_c c;
    always_ff @(posedge clk) begin
        if (c == null) begin
            c      = new();
            c.data = din;
            dout   <= din;
        end else begin
            c.data = din;
            dout   <= c.incr();
        end
    end
endmodule
module enum_fsm (
    input  logic clk,
    input  logic rst,
    output logic done
);
    typedef enum logic [1:0] {IDLE, RUN, DONE} state_t;
    state_t state;
    always_ff @(posedge clk or posedge rst) begin
        if (rst)
            state <= IDLE;
        else begin
            unique case (state)
                IDLE : state <= RUN;
                RUN  : state <= DONE;
                DONE : state <= DONE;
            endcase
        end
    end
    assign done = (state == DONE);
endmodule
module chain_or #(parameter N = 4) (
    input  logic [N-1:0] vector,
    output logic         y
);
    genvar i;
    wire [N-1:0] inter;
    assign inter[0] = vector[0];
    generate
        for (i = 1; i < N; i = i + 1) begin : g
            assign inter[i] = inter[i-1] | vector[i];
        end
    endgenerate
    assign y = inter[N-1];
endmodule
module if_example #(parameter WIDTH = 8) (
    input  logic [WIDTH-1:0] in_data,
    output logic             ready
);
    simple_if #(.WIDTH(WIDTH)) i();
    assign i.data = in_data;
    assign i.en   = 1'b1;
    assign ready  = i.en;
endmodule
module queue_example (
    input  logic       clk,
    input  logic [7:0] din,
    output logic [7:0] dout
);
    byte q[$];
    always_ff @(posedge clk) begin
        q.push_back(din);
        if (q.size() > 4) q.pop_front();
        dout <= q[0];
    end
endmodule
module unique_case_example (
    input  logic [1:0] sel,
    output logic       y
);
    always_comb begin
        unique case (sel)
            2'b00: y = 1'b0;
            2'b01: y = 1'b1;
            default: y = 1'b0;
        endcase
    end
endmodule
module dynamic_mux #(parameter W = 8) (
    input  logic [W-1:0] in0,
    input  logic [W-1:0] in1,
    input  logic         sel,
    output logic [W-1:0] out
);
    assign out = sel ? in1 : in0;
endmodule
