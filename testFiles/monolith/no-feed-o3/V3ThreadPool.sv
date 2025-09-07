`timescale 1ns/1ps
module mod_add_generate #(parameter W = 32) (
    input  logic [W-1:0] a,
    input  logic [W-1:0] b,
    output logic [W:0]   sum
);
    function automatic [W:0] add_f(input logic [W-1:0] x, input logic [W-1:0] y);
        add_f = x + y;
    endfunction
    always_comb sum = add_f(a, b);
endmodule
module mod_state_fsm (
    input  logic clk,
    input  logic rst_n,
    input  logic in_sig,
    output logic done
);
    typedef enum logic [1:0] {IDLE = 2'b00, BUSY = 2'b01, DONE = 2'b10} state_e;
    state_e state, nxt;
    always_comb begin
        nxt = state;
        case (state)
            IDLE : if (in_sig) nxt = BUSY;
            BUSY : nxt = DONE;
            DONE : if (!in_sig) nxt = IDLE;
            default : nxt = IDLE;
        endcase
    end
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) state <= IDLE;
        else        state <= nxt;
    end
    assign done = (state == DONE);
endmodule
module mod_class_accum #(parameter WIDTH = 32) (
    input  logic             clk,
    input  logic             rst_n,
    input  logic [WIDTH-1:0] din,
    output logic [WIDTH-1:0] dout
);
    class accum_c;
        int total;
        function new(); total = 0; endfunction
        function int add(input int v); total += v; return total; endfunction
    endclass
    accum_c acc;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            acc = new();
            dout <= '0;
        end else begin
            if (acc == null) acc = new();
            dout <= acc.add(din);
        end
    end
endmodule
module mod_struct_union (
    input  logic [31:0] in_data,
    output logic [31:0] out_data
);
    typedef struct packed {
        logic [7:0] byte0, byte1, byte2, byte3;
    } bytes_t;
    typedef union packed {
        bytes_t      s;
        logic [31:0] w;
    } u_t;
    u_t u;
    always_comb begin
        u.w   = in_data;
        out_data = {u.s.byte3, u.s.byte2, u.s.byte1, u.s.byte0};
    end
endmodule
module mod_assert_property (
    input  logic clk,
    input  logic sig_in,
    output logic sig_out
);
    assign sig_out = sig_in;
    property p_no_X;
        @(posedge clk) !(sig_in === 1'bx);
    endproperty
    assert property (p_no_X);
endmodule
module mod_array_mem #(
    parameter WIDTH = 8,
    parameter DEPTH = 16
) (
    input  logic                     clk,
    input  logic                     wr_en,
    input  logic [$clog2(DEPTH)-1:0] addr,
    input  logic [WIDTH-1:0]         din,
    output logic [WIDTH-1:0]         dout
);
    logic [WIDTH-1:0] mem [0:DEPTH-1];
    always_ff @(posedge clk) begin
        if (wr_en) mem[addr] <= din;
        dout <= mem[addr];
    end
endmodule
module mod_function_crc (
    input  logic [31:0] data_in,
    output logic [31:0] crc_out
);
    function automatic [31:0] crc32(input logic [31:0] data);
        logic [31:0] crc;
        integer i;
        crc = 32'hFFFFFFFF;
        for (i = 0; i < 32; i++) begin
            if (crc[0] ^ data[i])
                crc = (crc >> 1) ^ 32'hEDB88320;
            else
                crc = (crc >> 1);
        end
        crc32 = ~crc;
    endfunction
    assign crc_out = crc32(data_in);
endmodule
module mod_enum_case (
    input  logic [3:0] sel,
    output logic       flag
);
    typedef enum logic [3:0] {
        ZERO  = 4'd0,
        ONE   = 4'd1,
        TWO   = 4'd2,
        THREE = 4'd3,
        FOUR  = 4'd4
    } sel_e;
    sel_e s;
    always_comb begin
        s = sel_e'(sel);
        unique case (s)
            ZERO      : flag = 1'b0;
            ONE, TWO  : flag = 1'b1;
            THREE     : flag = 1'b0;
            default   : flag = 1'b1;
        endcase
    end
endmodule
module mod_shift_reg #(
    parameter W = 8
) (
    input  logic         clk,
    input  logic         rst,
    input  logic [W-1:0] din,
    output logic [W-1:0] dout
);
    logic [W-1:0] q;
    always_ff @(posedge clk or posedge rst) begin
        if (rst) q <= '0;
        else     q <= {q[W-2:0], din[W-1]};
    end
    assign dout = q;
endmodule
module mod_lfsr (
    input  logic clk,
    input  logic rst,
    output logic [15:0] lfsr_out
);
    logic [15:0] r;
    always_ff @(posedge clk or posedge rst) begin
        if (rst) r <= 16'hACE1;
        else     r <= {r[14:0], r[15] ^ r[14] ^ r[12] ^ r[3]};
    end
    assign lfsr_out = r;
endmodule
module mod_counter #(
    parameter W = 16
) (
    input  logic         clk,
    input  logic         rst_n,
    input  logic         en,
    output logic [W-1:0] count
);
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) count <= '0;
        else if (en) count <= count + 1'b1;
    end
endmodule
module mod_pipeline #(
    parameter W = 32,
    parameter STAGES = 4
) (
    input  logic         clk,
    input  logic         rst_n,
    input  logic [W-1:0] din,
    output logic [W-1:0] dout
);
    logic [W-1:0] pipe [0:STAGES-1];
    integer i;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            for (i = 0; i < STAGES; i++) pipe[i] <= '0;
        end else begin
            pipe[0] <= din;
            for (i = 1; i < STAGES; i++) pipe[i] <= pipe[i-1];
        end
    end
    assign dout = pipe[STAGES-1];
endmodule
module mod_logic_vector (
    input  logic [15:0] a,
    input  logic [15:0] b,
    output logic [15:0] y_and,
    output logic [15:0] y_or,
    output logic [15:0] y_xor
);
    assign y_and = a & b;
    assign y_or  = a | b;
    assign y_xor = a ^ b;
endmodule
module mod_reduction (
    input  logic [31:0] in_vec,
    output logic        parity
);
    assign parity = ^in_vec;
endmodule
module mod_priority_encoder (
    input  logic [15:0] req,
    output logic [3:0]  enc,
    output logic        valid
);
    integer i;
    always_comb begin
        enc   = 4'd0;
        valid = 1'b0;
        for (i = 15; i >= 0; i--) begin
            if (req[i]) begin
                enc   = i[3:0];
                valid = 1'b1;
            end
        end
    end
endmodule
