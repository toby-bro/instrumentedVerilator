package util_pkg;
    typedef struct packed {
        logic [7:0] a;
        logic [7:0] b;
    } byte_pair_t;
endpackage
interface bus_if #(parameter W = 8) (input logic clk);
    logic [W-1:0] data;
    modport master (input  clk, output data);
    modport slave  (input  clk, input  data);
endinterface
module dpi_adder #(parameter W = 32)
   (input  logic                    clk,
    input  logic [W-1:0]            a,
    input  logic [W-1:0]            b,
    output logic [W-1:0]            sum);
    import "DPI-C" function int c_add (input int x, input int y);
    always_ff @(posedge clk) begin
        sum <= c_add(a, b);
    end
endmodule
module cover_example
   (input  logic clk,
    input  logic reset_n,
    input  logic in_sig,
    output logic out_sig);
    property p_transfer;
        @(posedge clk) disable iff(!reset_n) in_sig |-> ##1 out_sig;
    endproperty
    cover property (p_transfer);
    always_ff @(posedge clk) begin
        if (!reset_n) out_sig <= 1'b0;
        else          out_sig <= in_sig;
    end
endmodule
module enum_example
   (input  logic       clk,
    input  logic [1:0] sel,
    output logic       y);
    typedef enum logic [1:0] {S0 = 2'b00, S1 = 2'b01, S2 = 2'b10} state_t;
    state_t state;
    always_ff @(posedge clk) begin
        state <= state_t'(sel);
        y     <= (state == S2);
    end
    assert property (@(posedge clk) state != 2'b11);
endmodule
module struct_union_example
   (input  logic        clk,
    input  logic [31:0] in_data,
    output logic [31:0] out_data);
    typedef struct packed {
        logic [15:0] lo;
        logic [15:0] hi;
    } halves_t;
    union packed {
        logic  [31:0] word;
        halves_t      halves;
    } data_u;
    always_ff @(posedge clk) begin
        data_u.word  <= in_data;
        out_data     <= {data_u.halves.hi, data_u.halves.lo};
    end
endmodule
module interface_user
   (input               dummy_in,
    bus_if.master       m,
    bus_if.slave        s,
    output logic        done);
    always_ff @(posedge m.clk) begin
        done <= s.data[0] ^ dummy_in;
    end
endmodule
module generate_example
   #(parameter N = 8)
   (input  logic [N-1:0] in_bus,
    output logic [N-1:0] out_bus);
    genvar i;
    generate
        for (i = 0; i < N; i++) begin : gen_blk
            assign out_bus[i] = in_bus[N-1-i];
        end
    endgenerate
endmodule
module func_example
   (input  logic              clk,
    input  logic signed [15:0] a,
    input  logic signed [15:0] b,
    output logic signed [15:0] y);
    function automatic logic signed [15:0] saturating_add
        (input logic signed [15:0] x, input logic signed [15:0] z);
        logic signed [16:0] sum;
        begin
            sum = x + z;
            if      (sum >  32767)  saturating_add =  32767;
            else if (sum < -32768)  saturating_add = -32768;
            else                    saturating_add = sum[15:0];
        end
    endfunction
    always_ff @(posedge clk) begin
        y <= saturating_add(a, b);
    end
endmodule
module array_example
   (input  logic              clk,
    input  logic [7:0]        in_data [0:3],
    output logic [7:0]        out_data[0:3]);
    always_ff @(posedge clk) begin : arr_proc
        int i;
        for (i = 0; i < 4; i++) begin
            out_data[i] <= in_data[3-i];
        end
    end
endmodule
