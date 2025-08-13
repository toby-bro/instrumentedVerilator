module stats_arith #(
    parameter WIDTH = 8
) (
    input  logic                    clk,
    input  logic [WIDTH-1:0]        in_data,
    output logic [WIDTH-1:0]        out_data
);
    genvar i;
    wire [WIDTH-1:0] temp;
    generate
        for (i = 0; i < WIDTH; i++) begin : gen_blk
            assign temp[i] = in_data[i] ^ i[0];
        end
    endgenerate
    always_ff @(posedge clk) begin
        out_data <= temp;
    end
endmodule
module stats_enum_struct (
    input  logic        clk,
    input  logic [3:0]  sel,
    output logic        flag
);
    typedef enum logic [1:0] { S0 = 2'b00, S1 = 2'b01, S2 = 2'b10, S3 = 2'b11 } state_e;
    typedef struct packed {
        state_e st;
        logic   parity;
    } st_info_s;
    st_info_s info;
    function automatic logic parity_calc (input logic [3:0] d);
        parity_calc = ^d;
    endfunction
    always_ff @(posedge clk) begin
        info.st     <= state_e'(sel[1:0]);
        info.parity <= parity_calc(sel);
        flag        <= (info.st == S2) & info.parity;
    end
endmodule
module stats_array #(
    parameter SIZE = 4
) (
    input  logic       clk,
    input  logic [7:0] din,
    output logic [7:0] dout
);
    logic [7:0] mem [0:SIZE-1];
    integer idx;
    always_ff @(posedge clk) begin
        for (idx = 0; idx < SIZE-1; idx++) begin
            mem[idx+1] <= mem[idx];
        end
        mem[0] <= din;
        dout   <= mem[SIZE-1];
    end
endmodule
module stats_assert (
    input  logic clk,
    input  logic reset_n,
    input  logic in_valid,
    output logic accept
);
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            accept <= 1'b0;
        end else begin
            accept <= in_valid;
        end
    end
    property hold_valid;
        @(posedge clk) disable iff (!reset_n) in_valid |-> ##1 accept;
    endproperty
    assert property (hold_valid);
endmodule
module stats_class (
    input  logic       clk,
    input  logic [7:0] a,
    output logic [7:0] b
);
    class adder_c;
        function automatic logic [7:0] add (input logic [7:0] x);
            return x + 8'd1;
        endfunction
    endclass
    adder_c c_h;
    always_ff @(posedge clk) begin
        if (c_h == null) c_h = new();
        b <= c_h.add(a);
    end
endmodule
module stats_union (
    input  logic [7:0] in_vec,
    output logic [7:0] out_vec
);
    typedef union packed {
        logic [7:0] vec;
        struct packed {
            logic [3:0] low;
            logic [3:0] high;
        } parts;
    } u_t;
    u_t u_data;
    always_comb begin
        u_data.vec = in_vec;
        out_vec    = {u_data.parts.high, u_data.parts.low};
    end
endmodule
module stats_cover (
    input  logic clk,
    input  logic data,
    output logic dummy
);
    always_ff @(posedge clk) begin
        dummy <= data;
    end
    cover property (@(posedge clk) data);
endmodule
