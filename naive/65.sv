module param_gen #(parameter int WIDTH = 8, parameter logic [3:0] MODE = 4'hA) (
    input  logic                   clk,
    input  logic [WIDTH-1:0]       in,
    output logic [WIDTH-1:0]       out
);
    localparam int DEPTH = 4;
    genvar i;
    logic [WIDTH-1:0] regs [0:DEPTH-1];
    generate
        for (i = 0; i < DEPTH; i = i + 1) begin : gen_loop
            assign regs[i] = in + i;
        end
    endgenerate
    assign out = regs[0] ^ MODE;
endmodule
module seq_reg (
    input  logic clk,
    input  logic d,
    output logic q
);
    always_ff @(posedge clk) begin
        q <= d;
    end
endmodule
module comb_logic (
    input  logic a,
    input  logic b,
    output logic y
);
    always_comb begin
        if (a)
            y = b;
        else
            y = ~b;
    end
endmodule
module struct_union_enum (
    input  logic [1:0] sel,
    input  logic [7:0] data_in,
    output logic [7:0] data_out
);
    typedef struct packed {
        logic        flag;
        logic [3:0]  nibble;
    } my_struct_t;
    typedef union packed {
        logic [4:0]  bits;
        my_struct_t  s;
    } my_union_t;
    typedef enum logic [1:0] {
        IDLE = 2'b00,
        BUSY = 2'b01,
        DONE = 2'b10
    } my_enum_t;
    my_union_t u;
    my_enum_t state;
    always_comb begin
        case (sel)
            2'b00: begin
                u.bits  = data_in[4:0];
                state   = IDLE;
            end
            2'b01: begin
                u.s.nibble = data_in[3:0];
                u.s.flag   = data_in[7];
                state      = BUSY;
            end
            2'b10: begin
                u.bits  = data_in[4:0];
                state   = DONE;
            end
            default: begin
                u.bits  = '0;
                state   = IDLE;
            end
        endcase
        data_out = {u.s.flag, u.s.nibble, ~u.s.flag};
    end
endmodule
module func_task (
    input  logic        clk,
    input  logic [3:0]  in_val,
    output logic [3:0]  out_val
);
    function logic [3:0] compute(input logic [3:0] x);
        compute = x + 1;
    endfunction
    task report(input logic [3:0] x);
        out_val = x;
    endtask
    always_ff @(posedge clk) begin
        logic [3:0] temp;
        temp = compute(in_val);
        report(temp);
    end
endmodule
module assertion_mod (
    input  logic sig,
    input  logic rst,
    output logic flag
);
    always_comb begin
        flag = 1'b0;
        assert (sig || rst) else flag = 1'b1;
    end
endmodule
module class_inst (
    input  logic        clk,
    input  logic [3:0]  a,
    output logic [3:0]  b
);
    class myClass;
        logic [3:0] data;
        function void set(input logic [3:0] d);
            data = d;
        endfunction
        function logic [3:0] get();
            return data;
        endfunction
    endclass
    logic [3:0] stored;
    always_ff @(posedge clk) begin
        static myClass inst = new();
        inst.set(a);
        stored <= inst.get();
    end
    assign b = stored;
endmodule
