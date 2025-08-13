timeunit 1ns/1ps;
timeprecision 1ps;
interface my_if #(parameter WIDTH = 8);
    timeunit 1ns/1ps;
    logic [WIDTH-1:0] a;
    modport mp (input a);
endinterface
package util_pkg;
    timeunit 1ns/1ps;
    typedef enum logic [1:0] {S_IDLE = 2'b00, S_RUN = 2'b01, S_STOP = 2'b10} state_t;
endpackage
module modA (
    input  logic [7:0] bus_in,
    input  logic       data,
    output logic [7:0] q
);
    timeunit 1ns/1ps;
    my_if #(8) intf();
    always_comb begin
        intf.a = bus_in;
        q = intf.a ^ {7'b0, data};
    end
endmodule
module modB #(
    parameter N = 2
) (
    input  logic [7:0] bus_in [N],
    input  logic       data,
    output logic [7:0] q
);
    timeunit 1ns/1ps;
    my_if #(8) intf();
    always_comb begin
        intf.a = bus_in[0];
        q = intf.a ^ {7'b0, data};
    end
endmodule
module modState (
    input  logic             data,
    input  util_pkg::state_t state,
    output logic             q
);
    timeunit 1ns/1ps;
    always_comb q = (state == util_pkg::S_RUN) & data;
endmodule
module modArray (
    input  logic [7:0]  data_in [4],
    output logic [31:0] flat
);
    timeunit 1ns/1ps;
    integer i;
    always_comb begin
        flat = 32'h0;
        for (i = 0; i < 4; i = i + 1) begin
            flat = flat | ({{24{1'b0}}, data_in[i]} << (i * 8));
        end
    end
endmodule
