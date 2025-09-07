module split_reorder_ff(
    input  logic        clk,
    input  logic        reset,
    input  logic [7:0]  d_in,
    output logic [7:0]  q_out
);
    always_ff @(posedge clk) begin
        if (reset) begin
            q_out <= '0;
        end else begin
            q_out <= d_in;
        end
    end
endmodule
module split_logic_if(
    input  logic  a,
    input  logic  b,
    output logic  y
);
    always_comb begin
        logic x;
        if (a && b) begin
            x = a;
        end else if (a || b) begin
            x = b;
        end else begin
            x = 1'b0;
        end
        y = x;
    end
endmodule
module split_case(
    input  logic [1:0]   sel,
    input  logic [7:0]   in0,
    input  logic [7:0]   in1,
    input  logic [7:0]   in2,
    output logic [7:0]   out
);
    always_comb begin
        case (sel)
            2'b00: out = in0;
            2'b01: out = in1;
            2'b10: out = in2;
            default: out = 8'hFF;
        endcase
    end
endmodule
module split_for_loop(
    input  logic [3:0]  in_bus,
    output logic [3:0]  out_bus
);
    always_comb begin
        integer i;
        for (i = 0; i < 4; i = i + 1) begin
            out_bus[i] = in_bus[i] ^ in_bus[3-i];
        end
    end
endmodule
module split_while_loop(
    input  logic        load,
    input  logic [7:0]  start_val,
    output logic [7:0]  result
);
    always_comb begin
        int count = 0;
        result = 0;
        if (load) begin
            result = start_val;
            while (count < 4) begin
                result = result + count;
                count++;
            end
        end
    end
endmodule
module split_cont_assign(
    input  logic a,
    input  logic b,
    output logic y
);
    assign y = a & b;
endmodule
module split_params #(
    parameter WIDTH = 8
)(
    input  logic                  clk,
    input  logic [WIDTH-1:0]      din,
    output logic [WIDTH-1:0]      dout
);
    always_ff @(posedge clk) begin
        dout <= din;
    end
endmodule
module split_array_ops(
    input  logic [7:0] arr_in  [3:0],
    output logic [7:0] arr_out [3:0]
);
    always_comb begin
        for (int i = 0; i < 4; i = i + 1) begin
            arr_out[i] = ~arr_in[i];
        end
    end
endmodule
module split_enum(
    input  logic [1:0]  state_in,
    output logic        go
);
    typedef enum logic [1:0] {IDLE, BUSY, DONE, ERROR} state_t;
    state_t cstate, nstate;
    always_comb begin
        cstate = state_in;
        case (cstate)
            IDLE:  nstate = BUSY;
            BUSY:  nstate = DONE;
            DONE:  nstate = IDLE;
            ERROR: nstate = ERROR;
            default: nstate = IDLE;
        endcase
        go = (nstate == BUSY);
    end
endmodule
module split_struct_union(
    input  logic        sel,
    input  logic [15:0] din,
    output logic [7:0]  dout
);
    typedef struct packed { logic [7:0] lo; logic [7:0] hi; } half_t;
    typedef union packed { half_t h; logic [15:0] full; } word_t;
    word_t w;
    always_comb begin
        w.full = din;
        if (sel) dout = w.hi; else dout = w.lo;
    end
endmodule
module split_function_call(
    input  logic [7:0] a,
    input  logic [7:0] b,
    output logic [7:0] sum
);
    function logic [7:0] add8(input logic [7:0] x, input logic [7:0] y);
        add8 = x + y;
    endfunction
    always_comb begin
        sum = add8(a, b);
    end
endmodule
module split_task_call(
    input  logic        clk,
    input  logic        rst,
    input  logic [3:0]  in_val,
    output logic [3:0]  out_val
);
    task automatic do_calc(input logic [3:0] iv, output logic [3:0] ov);
        ov = iv * 2;
    endtask
    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            out_val <= 0;
        end else begin
            do_calc(in_val, out_val);
        end
    end
endmodule
module split_class_inst(
    input  logic        clk,
    input  logic        rst,
    input  logic [3:0]  d,
    output logic [3:0]  q
);
    class Reg;
        rand logic [3:0] r;
        function void write(input logic [3:0] v); r = v; endfunction
        function logic [3:0] read(); return r; endfunction
    endclass
    Reg reg_inst;
    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            reg_inst = new();
            q <= 0;
        end else begin
            reg_inst.write(d);
            q <= reg_inst.read();
        end
    end
endmodule
module split_generate_if(
    input  logic [7:0] in,
    input  logic       en,
    output logic [7:0] out
);
    generate
        if (1) begin
            assign out = en ? in : 8'hAA;
        end
    endgenerate
endmodule
module split_generate_for(
    input  logic        sel,
    input  logic [7:0]  din [1:0],
    output logic [7:0]  dout [1:0]
);
    genvar i;
    generate
        for (i = 0; i < 2; i = i + 1) begin : gen_blk
            assign dout[i] = sel ? din[i] : 8'h55;
        end
    endgenerate
endmodule
