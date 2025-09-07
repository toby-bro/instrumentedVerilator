package util_pkg;
    class Accumulator;
        int sum;
        function new(int v = 0);
            sum = v;
        endfunction
        function void add(int v);
            sum += v;
        endfunction
    endclass
endpackage
module mod_dpi (
    input  logic        clk,
    input  logic [31:0] a,
    input  logic [31:0] b,
    output logic [31:0] y
);
    int result /* verilator public */;
    import "DPI-C" function int dpi_c_add (input int unsigned lhs, input int unsigned rhs);
    export "DPI-C" function dpi_sv_inc;
    function int dpi_sv_inc (input int unsigned v);
        dpi_sv_inc = v + 1;
    endfunction
    always_comb begin
        result = dpi_c_add(a, b);
        y      = result;
    end
endmodule
module mod_arrays #(
    parameter int WIDTH = 8,
    parameter string ID = "ARR"
) (
    input  logic                  sel,
    input  logic [WIDTH-1:0]      din,
    output logic [WIDTH-1:0]      dout
);
    logic [WIDTH-1:0] packed_vec [0:3];
    logic [3:0][WIDTH-1:0] packed_mat /* verilator public_flat */;
    always_comb begin
        packed_vec[0] = din;
        packed_mat[0] = din;
        dout = sel ? packed_vec[0] : packed_mat[0];
    end
endmodule
module mod_cover (
    input  logic clk,
    input  logic reset_n,
    input  logic sig_a,
    input  logic sig_b,
    output logic covered
);
    assign covered = sig_a & sig_b;
    property p_transfer;
        disable iff (!reset_n)
            sig_a |=> sig_b;
    endproperty
    cover property (@(posedge clk) p_transfer);
endmodule
timeunit 1ns/1ps;
module mod_time (
    input  logic       clk,
    input  logic [7:0] d_in,
    output logic [7:0] d_out
);
    always_ff @(posedge clk) begin
        d_out <= d_in;
    end
endmodule
module mod_class (
    input  logic        clk,
    input  logic [31:0] in_data,
    output logic [31:0] out_data
);
    util_pkg::Accumulator acc_handle = null;
    always_ff @(posedge clk) begin
        if (acc_handle == null) begin
            acc_handle = new(in_data);
        end else begin
            acc_handle.add(in_data);
        end
        out_data <= acc_handle.sum;
    end
endmodule
module mod_event (
    input  logic clk,
    input  logic trigger,
    output logic toggled
);
    event ev;
    logic state;
    always_ff @(posedge clk) begin
        if (trigger) -> ev;
    end
    always_ff @(posedge clk) begin
        state   <= trigger;
        toggled <= state;
    end
endmodule
