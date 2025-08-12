module arithmetic_unit #(parameter WIDTH = 8) (
    input  logic [WIDTH-1:0] a,
    input  logic [WIDTH-1:0] b,
    input  logic             op,      
    output logic [WIDTH-1:0] result,
    output logic             carry
);
    always_comb begin
        unique case (op)
            1'b0: {carry, result} = a + b;
            1'b1: {carry, result} = a - b;
            default: {carry, result} = '0;
        endcase
    end
endmodule
module pipelined_acc #(parameter WIDTH = 16, DEPTH = 4) (
    input  logic                 clk,
    input  logic                 reset,
    input  logic [WIDTH-1:0]     data_in,
    output logic [WIDTH-1:0]     data_out
);
    logic [WIDTH-1:0] stage [DEPTH-1:0];
    int i;
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            for (i = 0; i < DEPTH; i++) stage[i] <= '0;
        end
        else begin
            stage[0] <= data_in;
            for (i = 1; i < DEPTH; i++) stage[i] <= stage[i-1];
        end
    end
    assign data_out = stage[DEPTH-1];
endmodule
module state_machine (
    input  logic clk,
    input  logic reset,
    input  logic go,
    output logic done
);
    typedef enum logic [1:0] {IDLE, BUSY, FINISH} state_t;
    state_t state;
    always_ff @(posedge clk or posedge reset) begin
        if (reset) state <= IDLE;
        else begin
            unique case (state)
                IDLE:   state <= go    ? BUSY   : IDLE;
                BUSY:   state <=              FINISH;
                FINISH: state <=              IDLE;
            endcase
        end
    end
    assign done = (state == FINISH);
endmodule
module packed_struct_example (
    input  logic [31:0] raw,
    output logic [7:0]  opcode,
    output logic [15:0] addr,
    output logic [3:0]  flags
);
    typedef struct packed {
        logic [7:0]  opcode;
        logic [15:0] addr;
        logic [3:0]  flags;
        logic [3:0]  reserved;
    } instr_t;
    instr_t instr;
    always_comb instr = instr_t'(raw);
    assign opcode = instr.opcode;
    assign addr   = instr.addr;
    assign flags  = instr.flags;
endmodule
module union_example (
    input  logic [31:0] data_in,
    input  logic        select,   
    output logic [7:0]  byte_sel
);
    typedef union packed {
        logic [31:0] word;
        struct packed {
            logic [7:0] b0;
            logic [7:0] b1;
            logic [7:0] b2;
            logic [7:0] b3;
        } bytes;
    } data_u;
    data_u data;
    always_comb data.word = data_in;
    assign byte_sel = select ? data.bytes.b1 : data.bytes.b0;
endmodule
module array_manip #(parameter WIDTH = 8, SIZE = 4) (
    input  logic                 clk,
    input  logic                 reset,
    input  logic [WIDTH-1:0]     din,
    output logic [WIDTH-1:0]     dout
);
    logic [WIDTH-1:0] mem [SIZE-1:0];
    integer idx;
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            for (idx = 0; idx < SIZE; idx++) mem[idx] <= '0;
        end
        else begin
            mem[0] <= din;
            for (idx = 1; idx < SIZE; idx++) mem[idx] <= mem[idx-1];
        end
    end
    assign dout = mem[SIZE-1];
endmodule
module class_usage (
    input  logic       clk,
    input  logic       reset,
    input  logic [7:0] val_in,
    output logic [7:0] sum_out
);
    class accumulator;
        bit [7:0] sum;
        function void add(bit [7:0] val);
            sum += val;
        endfunction
        function bit [7:0] get();
            return sum;
        endfunction
    endclass
    accumulator acc;
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            acc = new();
        end
        else begin
            if (acc == null) acc = new();
            acc.add(val_in);
        end
        sum_out <= acc.get();
    end
endmodule
module function_task_example (
    input  logic [15:0] a,
    input  logic [15:0] b,
    output logic        eq
);
    function automatic bit parity_even(bit [15:0] v);
        return (^v) == 0;
    endfunction
    always_comb eq = (a == b) && parity_even(a ^ b);
endmodule
