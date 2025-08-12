package util_pkg;
    typedef enum logic [2:0] {
        OP_ADD,
        OP_SUB,
        OP_AND,
        OP_OR,
        OP_XOR
    } op_t;
    typedef struct packed {
        logic [3:0] a;
        logic [3:0] b;
        op_t        op;
    } alu_cmd_t;
endpackage : util_pkg
//------------------------------------------------------------
//------------------------------------------------------------
module param_adder #(
    parameter int WIDTH = 8
) (
    input  logic [WIDTH-1:0]  in_a,
    input  logic [WIDTH-1:0]  in_b,
    output logic [WIDTH   :0] out_sum
);
    typedef struct packed {
        logic [WIDTH-1:0] a;
        logic [WIDTH-1:0] b;
    } add_operands_t;
    add_operands_t ops;
    always_comb begin
        ops.a     = in_a;
        ops.b     = in_b;
        out_sum   = ops.a + ops.b;
    end
endmodule
//------------------------------------------------------------
//------------------------------------------------------------
module state_machine_enum (
    input  logic clk,
    input  logic rst_n,
    input  logic start,
    output logic done
);
    typedef enum logic [1:0] {
        IDLE,
        BUSY,
        COMPLETE
    } state_t;
    state_t state, next_state;
    always_comb begin
        next_state = state;
        case (state)
            IDLE:     if (start)   next_state = BUSY;
            BUSY:     if (!start)  next_state = COMPLETE;
            COMPLETE:              next_state = IDLE;
            default:               next_state = IDLE;
        endcase
    end
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            state <= IDLE;
        else
            state <= next_state;
    end
    assign done = (state == COMPLETE);
endmodule
//------------------------------------------------------------
//------------------------------------------------------------
module class_in_proc (
    input  logic [3:0] in_val,
    output logic [3:0] out_val
);
    class mult_c;
        function automatic int mult (int x);
            return x * 2;
        endfunction
    endclass : mult_c
    always_comb begin
        automatic mult_c mc = new();
        out_val = mc.mult(in_val);
    end
endmodule
//------------------------------------------------------------
//------------------------------------------------------------
module struct_union_demo (
    input  logic [7:0] in_byte,
    output logic [7:0] out_byte
);
    typedef struct packed {
        logic [3:0] high;
        logic [3:0] low;
    } nibble_t;
    typedef union packed {
        nibble_t nibbles;
        logic [7:0] whole;
    } byte_u;
    byte_u val;
    always_comb begin
        val.whole  = in_byte;
        out_byte   = {val.nibbles.low, val.nibbles.high}; 
    end
endmodule
//------------------------------------------------------------
//------------------------------------------------------------
module generate_demo #(
    parameter int N = 8
) (
    input  logic [N-1:0] in_vec,
    output logic [N-1:0] out_vec
);
    genvar i;
    generate
        for (i = 0; i < N; i++) begin : bit_swap
            assign out_vec[i] = in_vec[N-1-i];
        end
    endgenerate
endmodule
//------------------------------------------------------------
//------------------------------------------------------------
module assert_demo (
    input  logic clk,
    input  logic req,
    input  logic grant,
    output logic passthru
);
    property grant_after_req;
        @(posedge clk) req |-> ##1 grant;
    endproperty
    assert property (grant_after_req);
    assign passthru = grant;
endmodule
//------------------------------------------------------------
//------------------------------------------------------------
module simple_alu (
    input  util_pkg::alu_cmd_t cmd,
    output logic [3:0]         result
);
    always_comb begin
        unique case (cmd.op)
            util_pkg::OP_ADD: result = cmd.a + cmd.b;
            util_pkg::OP_SUB: result = cmd.a - cmd.b;
            util_pkg::OP_AND: result = cmd.a & cmd.b;
            util_pkg::OP_OR : result = cmd.a | cmd.b;
            util_pkg::OP_XOR: result = cmd.a ^ cmd.b;
            default         : result = '0;
        endcase
    end
endmodule
