module stratum_test_1 #(parameter W = 32) (
    input  logic                 clk,
    input  logic [W-1:0]         in_data,
    output logic [W-1:0]         out_data
);
    logic                        bit1;
    logic [7:0]                  byte1;
    logic [15:0]                 halfword;
    logic [31:0]                 word;
    logic [63:0]                 dword;
    logic [127:0]                bigword;
    logic [7:0]                  unpacked_arr [0:3];
    logic [31:0]                 register_array [0:1][0:1];
    always_ff @(posedge clk) begin
        bit1                     <= in_data[0];
        byte1                    <= in_data[7:0];
        halfword                 <= in_data[15:0];
        word                     <= in_data[31:0];
        dword                    <= {2{in_data[31:0]}};
        bigword                  <= {4{in_data[31:0]}};
        unpacked_arr[0]          <= in_data[7:0];
        register_array[0][0]     <= in_data;
    end
    assign out_data = word;
endmodule
module function_call_mod (
    input  logic        clk,
    input  logic [31:0] in_val,
    output logic [31:0] out_val
);
    logic [31:0] accum;
    function automatic logic [31:0] inc(input logic [31:0] x);
        inc = x + 32'd1;
    endfunction
    always_ff @(posedge clk) begin
        accum <= inc(in_val);
    end
    assign out_val = accum;
endmodule
module struct_mod (
    input  logic        clk,
    input  logic [7:0]  data_in,
    output logic [7:0]  data_out
);
    typedef struct packed {
        logic [3:0] a;
        logic [3:0] b;
    } packed_t;
    packed_t p_var;
    packed_t array_of_struct [0:3];
    always_ff @(posedge clk) begin
        p_var.a            <= data_in[3:0];
        p_var.b            <= data_in[7:4];
        array_of_struct[0] <= p_var;
    end
    assign data_out = {p_var.b, p_var.a};
endmodule
module static_func_var_mod (
    input  logic clk,
    input  logic din,
    output logic dout
);
    function automatic logic stateful(input logic i);
        static logic prev;
        prev = i;
        stateful = prev;
    endfunction
    assign dout = stateful(din);
endmodule
module multidim_unpack_mod (
    input  logic        clk,
    input  logic [3:0]  idx,
    output logic [7:0]  out_byte
);
    logic [7:0] mem [0:3][0:3];
    always_ff @(posedge clk) begin
        mem[idx][idx] <= idx;
    end
    assign out_byte = mem[idx][idx];
endmodule
module param_mod #(
    parameter WIDTH = 24
) (
    input  logic                clk,
    input  logic [WIDTH-1:0]    in_bus,
    output logic [WIDTH-1:0]    out_bus
);
    logic [WIDTH-1:0] reg_bus;
    always_ff @(posedge clk) begin
        reg_bus <= in_bus;
    end
    assign out_bus = reg_bus;
endmodule
module clock_affinity_mod (
    input  logic clk,
    input  logic rst_n,
    output logic toggled
);
    logic state;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) state <= 1'b0;
        else        state <= ~state;
    end
    assign toggled = state;
endmodule
module array_unpack_mod (
    input  logic [3:0] sel,
    output logic [7:0] data_o
);
    logic [7:0] rom [0:15] = '{8'd0,8'd1,8'd2,8'd3,8'd4,8'd5,8'd6,8'd7,8'd8,8'd9,8'd10,8'd11,8'd12,8'd13,8'd14,8'd15};
    assign data_o = rom[sel];
endmodule
module opaque_struct_mod (
    input  logic        clk,
    input  logic [31:0] in_word,
    output logic [31:0] out_word
);
    typedef struct packed {
        logic [15:0] hi;
        logic [15:0] lo;
    } opaque_t;
    opaque_t data_s;
    always_ff @(posedge clk) begin
        data_s.hi <= in_word[31:16];
        data_s.lo <= in_word[15:0];
    end
    assign out_word = {data_s.hi, data_s.lo};
endmodule
module large_array_mod (
    input  logic [7:0]  addr,
    output logic [31:0] q
);
    logic [31:0] big_mem [0:255] = '{default:32'd0};
    assign q = big_mem[addr];
endmodule
