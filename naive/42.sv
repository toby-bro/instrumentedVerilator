interface bus_if #(parameter WIDTH = 8) (input logic clk);
    logic [WIDTH-1:0] data;
    logic             valid;
    modport m (input  clk, output data, output valid);
    modport s (input  clk, input  data, input  valid);
endinterface
//-----------------------------------------------------------------------------
//-----------------------------------------------------------------------------
module simple_pipe (
    input  logic        clk,
    input  logic [7:0]  in_data,
    output logic [7:0]  out_data
);
    logic [7:0] stage1;
    always_ff @(posedge clk) begin
        stage1   <= in_data;
        out_data <= stage1;
    end
endmodule
//-----------------------------------------------------------------------------
//-----------------------------------------------------------------------------
module struct_union_mod (
    input  logic [31:0] din,
    output logic [31:0] dout
);
    typedef struct packed {
        logic [15:0] low;
        logic [15:0] high;
    } word_t;
    typedef union packed {
        word_t       w;
        logic [31:0] raw;
    } u_word;
    always_comb begin
        u_word u;
        u.raw = din;
        dout  = {u.w.high, u.w.low};
    end
endmodule
//-----------------------------------------------------------------------------
//-----------------------------------------------------------------------------
module enum_fsm_mod (
    input  logic clk,
    input  logic rst,
    output logic done
);
    typedef enum logic [1:0] {IDLE, RUN, FINISH} state_t;
    state_t state, next;
    always_comb begin
        unique case (state)
            IDLE   : next = RUN;
            RUN    : next = FINISH;
            FINISH : next = FINISH;
            default: next = IDLE;
        endcase
    end
    always_ff @(posedge clk or posedge rst) begin
        if (rst) state <= IDLE;
        else     state <= next;
    end
    assign done = (state == FINISH);
endmodule
//-----------------------------------------------------------------------------
//-----------------------------------------------------------------------------
module func_task_mod (
    input  logic [7:0] in_val,
    output logic [7:0] out_val
);
    function automatic [7:0] swap_nibbles (input [7:0] v);
        swap_nibbles = {v[3:0], v[7:4]};
    endfunction
    task automatic saturate (input [7:0] v, output [7:0] r);
        if (v > 8'hF0) r = 8'hF0;
        else           r = v;
    endtask
    always_comb begin
        logic [7:0] tmp;
        tmp = swap_nibbles(in_val);
        saturate(tmp, out_val);
    end
endmodule
//-----------------------------------------------------------------------------
//-----------------------------------------------------------------------------
module class_demo_mod (
    input  logic        trigger,
    output logic [15:0] acc
);
    class Accumulator;
        int value;
        function new (); value = 0; endfunction
        function void add (input int v); value += v; endfunction
        function int  get (); return value; endfunction
    endclass
    Accumulator a_h;
    always_ff @(posedge trigger) begin
        if (a_h == null) a_h = new();
        a_h.add(1);
        acc <= a_h.get();
    end
endmodule
//-----------------------------------------------------------------------------
//-----------------------------------------------------------------------------
module assert_prop_mod (
    input  logic clk,
    input  logic req,
    input  logic ack,
    output logic ok
);
    property handshakeP;
        @(posedge clk) req |-> ##1 ack;
    endproperty
    assert property (handshakeP);
    assign ok = ack;
endmodule
//-----------------------------------------------------------------------------
//-----------------------------------------------------------------------------
module parameterized_generate_mod #(
    parameter WIDTH = 16
) (
    input  logic [WIDTH-1:0] din,
    output logic [WIDTH-1:0] dout
);
    genvar i;
    generate
        for (i = 0; i < WIDTH; i++) begin : bit_reverse
            assign dout[i] = din[WIDTH-1-i];
        end
    endgenerate
endmodule
//-----------------------------------------------------------------------------
//-----------------------------------------------------------------------------
module multi_dim_array_mod (
    input  logic [7:0]  idx,
    output logic [31:0] value
);
    logic [31:0] mem [0:255];
    always_comb begin
        value = mem[idx];
    end
endmodule
//-----------------------------------------------------------------------------
//-----------------------------------------------------------------------------
module interface_user_mod (
    input  logic clk,
    output logic v
);
    bus_if #(8) if_inst (clk);
    always_ff @(posedge clk) begin
        if_inst.data  <= if_inst.data + 8'd1;
        if_inst.valid <= 1'b1;
    end
    assign v = if_inst.valid;
endmodule
//-----------------------------------------------------------------------------
//-----------------------------------------------------------------------------
module randomize_mod (
    input  logic       clk,
    output logic [3:0] rand_val
);
    always_ff @(posedge clk) begin
        rand_val <= $urandom_range(0, 15);
    end
endmodule
