timeunit 1ns;
timeprecision 1ps;
package data_pkg;
    typedef struct packed {
        logic [15:0] x;
        logic [15:0] y;
    } vec_t;
    typedef enum logic [1:0] {IDLE, RUN, DONE} state_t;
endpackage
interface simple_if;
    logic        valid;
    logic        ready;
    logic [7:0]  data;
    modport master (output valid, output data, input ready);
    modport slave  (input  valid, input  data, output ready);
endinterface
interface bus_if #(parameter int DW = 8);
    logic [DW-1:0] d;
    logic          vld;
    modport tx (output d, output vld);
    modport rx (input  d, input  vld);
endinterface
module timed_mod
    (input  logic in_sig,
     output logic out_sig);
    timeunit 1ns;
    timeprecision 1ps;
    always_comb out_sig = in_sig;
endmodule
module alpha
    (input  logic sig,
     output logic sig_out);
    always_comb sig_out = sig;
endmodule
module beta
    (input  logic sig,
     output logic sig_out);
    always_comb sig_out = ~sig;
endmodule
module struct_user
    (input  logic             clk,
     input  data_pkg::vec_t   in_vec,
     output data_pkg::vec_t   out_vec);
    data_pkg::vec_t temp_vec;
    always_comb begin
        temp_vec.x = in_vec.y;
        temp_vec.y = in_vec.x;
    end
    assign out_vec = temp_vec;
endmodule
module iface_master
    (input  logic enable,
     input  logic ready,
     output logic [7:0] data_out,
     output logic       valid_out,
     output logic       tx_done);
    simple_if if_inst();
    always_comb begin
        if_inst.valid = enable;
        if_inst.data  = 8'hA5;
        if_inst.ready = ready;
        data_out      = if_inst.data;
        valid_out     = if_inst.valid;
        tx_done       = if_inst.ready & enable;
    end
endmodule
module iface_array_user
    (input  logic [1:0] vld_in,
     output logic [1:0] vld_out);
    bus_if #(8) if_arr[2] ();
    genvar i;
    generate
        for (i = 0; i < 2; i++) begin : GEN_IF_TX
            localparam logic [7:0] CONST_DATA = i;
            always_comb begin
                if_arr[i].d   = CONST_DATA;
                if_arr[i].vld = vld_in[i];
                vld_out[i]    = if_arr[i].vld;
            end
        end
    endgenerate
endmodule
module default_time
    (input  logic in_a,
     output logic out_a);
    always_comb out_a = in_a;
endmodule
