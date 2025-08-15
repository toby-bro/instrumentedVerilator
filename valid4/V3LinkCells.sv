module mod_main (
    input logic clk,
    input logic rst_n,
    output logic [7:0] main_out
);
    typedef struct packed {
        logic [3:0] field_a;
        logic [3:0] field_b;
    } my_struct_t;
    my_struct_t s_main_data;
    logic main_sig_a;
    logic main_sig_b;
    logic main_sig_c;
    logic main_sig_d;
    logic main_sig_e;
    logic recur_res;
    logic cycle_res;
    logic missing_port_wire;
    mod_hier_top u_hier_top (
        .in_a           (main_sig_a),
        .in_b           (main_sig_b),
        .out_c          (main_sig_c),
        .top_missing_port(missing_port_wire)
    );
    mod_with_params #(.PARAM_WIDTH(16), .PARAM_VALUE(123)) u_mod_with_params (
        .p_in (main_sig_d),
        .p_out(main_sig_e)
    );
    mod_recursive #(.MAX_DEPTH(2)) u_recursive_inst (
        .recur_in (main_sig_c),
        .recur_out(recur_res)
    );
    mod_recursive_cycle_A u_recursive_cycle (
        .in_r_a (main_sig_c),
        .out_r_a(cycle_res)
    );
    pkg_types::my_class #(.CLASS_PARAM(5)) my_class_inst;
    logic [31:0] class_result;
    always_comb begin
        s_main_data.field_a = main_sig_a ? 4'hA : 4'hB;
        s_main_data.field_b = main_sig_b ? 4'hC : 4'hD;
        main_out = {s_main_data.field_a, s_main_data.field_b};
        if (my_class_inst == null) begin
            my_class_inst = new();
        end
        class_result = my_class_inst.calculate_sum(main_out[3:0], main_out[7:4]);
    end
    assign main_sig_a = clk;
    assign main_sig_b = rst_n;
    assign main_sig_d = main_out[0];
    assign missing_port_wire = 1'b0;
endmodule
module mod_hier_top (
    input logic in_a,
    input logic in_b,
    output logic out_c,
    input logic top_missing_port
);
    import pkg_types::*;
    logic mid_sig_f;
    logic iface_signal_req, iface_signal_ack;
    logic wire_for_missing_port;
    iface_bus bus_inst_a();
    assign bus_inst_a.request = in_a;
    assign iface_signal_req = bus_inst_a.request;
    assign bus_inst_a.acknowledge = in_b;
    assign iface_signal_ack = bus_inst_a.acknowledge;
    mod_hier_mid u_hier_mid (
        .in_d         (in_a),
        .in_e         (in_b),
        .out_f        (mid_sig_f),
        .if_in        (bus_inst_a),
        .modport_in   (bus_inst_a.master_mp),
        .missing_port (wire_for_missing_port)
    );
    assign out_c = mid_sig_f ^ in_a ^ in_b;
    assign wire_for_missing_port = top_missing_port;
endmodule
module mod_hier_mid (
    input logic in_d,
    input logic in_e,
    iface_bus.slave_mp if_in,
    iface_bus.master_mp modport_in,
    output logic out_f,
    input logic missing_port
);
    typedef enum logic [1:0] {
        STATE_IDLE,
        STATE_ACTIVE,
        STATE_DONE
    } fsm_state_t;
    fsm_state_t current_state;
    logic leaf_in_1;
    logic leaf_in_2;
    logic leaf_out_1;
    logic bind_in_sig;
    logic bind_out_sig;
    virtual iface_bus v_bus_inst;
    mod_hier_leaf u_hier_leaf (
        .leaf_in_1 (leaf_in_1),
        .leaf_in_2 (leaf_in_2)
    );
    bind mod_hier_leaf mod_for_bind_target bind_inst (.bind_in(bind_in_sig), .bind_out(bind_out_sig));
    always_comb begin
        leaf_in_1 = in_d;
        leaf_in_2 = in_e;
        out_f = leaf_out_1 ^ if_in.valid;
        current_state = STATE_IDLE;
        modport_in.data = {in_d, in_e};
        modport_in.start = in_d & in_e;
        bind_in_sig = in_d & in_e;
        v_bus_inst = if_in;
    end
    assign bind_out_sig = missing_port;
endmodule
module mod_hier_leaf (
    input logic leaf_in_1,
    input logic leaf_in_2,
    output logic leaf_out_1
);
    logic local_var_a;
    logic [3:0] local_var_b = 4'h5;
    assign local_var_a = leaf_in_1 & leaf_in_2;
    assign leaf_out_1 = local_var_a ^ local_var_b[0];
endmodule
module mod_recursive #(parameter MAX_DEPTH = 1) (
    input logic recur_in,
    output logic recur_out
);
    logic next_recur_out;
    generate
        if (MAX_DEPTH > 0) begin : gen_recur
            mod_recursive #(.MAX_DEPTH(MAX_DEPTH - 1)) u_next_recur (
                .recur_in (recur_in),
                .recur_out(next_recur_out)
            );
            assign recur_out = next_recur_out;
        end else begin : gen_no_recur
            assign recur_out = recur_in;
        end
    endgenerate
endmodule
package pkg_types;
    parameter PKG_PARAM_OFFSET = 10;
    typedef enum {
        RED, GREEN, BLUE
    } color_e;
    typedef struct packed {
        logic [7:0] data;
        logic valid;
    } data_s;
    typedef union packed {
        logic [15:0] word;
        struct packed { logic [7:0] byte0; logic [7:0] byte1; } bytes;
    } my_union_u;
    class my_class #(parameter CLASS_PARAM = 0);
        function new();
        endfunction
        function automatic int calculate_sum(int a, int b);
            return a + b + PKG_PARAM_OFFSET + CLASS_PARAM;
        endfunction
    endclass
    function int pkg_function (int val);
        return val + PKG_PARAM_OFFSET;
    endfunction
endpackage
interface iface_bus;
    logic request;
    logic acknowledge;
    logic [15:0] data;
    logic valid;
    logic start;
    modport master_mp (
        output request,
        input acknowledge,
        output data,
        output valid,
        output start
    );
    modport slave_mp (
        input request,
        output acknowledge,
        input data,
        input valid,
        input start
    );
endinterface
module mod_with_iface_array (
    input logic [3:0] array_in,
    output logic [3:0] array_out
);
    iface_bus bus_array[4]();
    genvar i;
    for (i = 0; i < 4; i++) begin : gen_bus
        assign bus_array[i].request = array_in[i];
        assign bus_array[i].valid = array_in[i];
        assign bus_array[i].acknowledge = !bus_array[i].request;
        assign bus_array[i].data = {i[1:0], i[1:0], i[1:0], i[1:0]};
        assign bus_array[i].start = array_in[i];
    end
    assign array_out[0] = bus_array[0].acknowledge;
    assign array_out[1] = bus_array[1].acknowledge;
    assign array_out[2] = bus_array[2].acknowledge;
    assign array_out[3] = bus_array[3].acknowledge;
endmodule
module mod_with_params #(parameter PARAM_WIDTH = 8, parameter PARAM_VALUE = 0) (
    input logic [PARAM_WIDTH-1:0] p_in,
    output logic [PARAM_WIDTH-1:0] p_out
);
    logic [PARAM_WIDTH-1:0] sub_sig_in;
    logic [PARAM_WIDTH-1:0] sub_sig_out;
    assign sub_sig_in = p_in + PARAM_VALUE;
    mod_sub_param #(.SUB_PARAM_WIDTH(PARAM_WIDTH)) u_sub_param (
        .sub_p_in  (sub_sig_in),
        .sub_p_out (sub_sig_out)
    );
    assign p_out = sub_sig_out;
endmodule
module mod_sub_param #(parameter SUB_PARAM_WIDTH = 8) (
    input logic [SUB_PARAM_WIDTH-1:0] sub_p_in,
    output logic [SUB_PARAM_WIDTH-1:0] sub_p_out
);
    assign sub_p_out = sub_p_in;
endmodule
module mod_for_bind_target (
    input logic bind_in,
    output logic bind_out
);
    assign bind_out = !bind_in;
endmodule
module mod_recursive_cycle_A (
    input logic in_r_a,
    output logic out_r_a
);
    logic next_r_b;
    mod_recursive_cycle_B u_b (.in_r_b(in_r_a), .out_r_b(next_r_b));
    assign out_r_a = next_r_b;
endmodule
module mod_recursive_cycle_B (
    input logic in_r_b,
    output logic out_r_b
);
    logic next_r_c;
    mod_recursive_cycle_C u_c (.in_r_c(in_r_b), .out_r_c(next_r_c));
    assign out_r_b = next_r_c;
endmodule
module mod_recursive_cycle_C (
    input logic in_r_c,
    output logic out_r_c
);
    assign out_r_c = ~in_r_c;
endmodule
