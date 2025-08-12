interface simple_if;
    logic sig;
    modport dut_mp (output sig);
    modport tb_mp  (input  sig);
endinterface
module array_pack_demo (
    input  logic [7:0] in_data,
    output logic [7:0] out_data
);
    logic [3:0][1:0] packed2d;
    logic [7:0]       unpacked_arr [0:3];
    always_comb begin
        packed2d        = {4{2'b10}};
        unpacked_arr[0] = in_data;
        out_data        = unpacked_arr[0];
    end
endmodule
module struct_union_demo (
    input  logic [3:0] in_sig,
    output logic [3:0] out_sig
);
    typedef struct packed {
        logic [3:0] a;
    } packed_s_t;
    typedef union packed {
        logic [3:0] a;
        logic [3:0] b;
    } packed_u_t;
    packed_s_t ps;
    packed_u_t pu;
    always_comb begin
        ps.a    = in_sig;
        pu.a    = ps.a;
        out_sig = pu.b;
    end
endmodule
module enum_demo (
    input  logic [1:0] sel,
    output logic       match
);
    typedef enum logic [1:0] {
        IDLE = 2'b00,
        BUSY = 2'b01,
        DONE = 2'b10
    } state_t;
    state_t current_state = BUSY;
    assign match = (current_state == sel);
endmodule
module typedef_param_demo #(
    parameter type T = logic [3:0]
) (
    input  T din,
    output T dout
);
    assign dout = din;
endmodule
module dpi_example (
    input  logic        clk,
    output logic [31:0] result
);
    import "DPI-C" function int c_add (input int a, input int b);
    always_ff @(posedge clk) begin
        result <= c_add(1, 2);
    end
endmodule
module vif_user (
    input  bit clk,
    output bit o
);
    virtual simple_if.dut_mp vif;
    bit state;
    always_ff @(posedge clk) begin
        state <= ~state;
        if (vif != null) begin
            vif.sig <= state;
        end
    end
    always_comb begin
        if (vif != null)
            o = vif.sig;
        else
            o = 1'b0;
    end
endmodule
module random_class_demo (
    input  logic       clk,
    output logic [7:0] random_value
);
    class rand_class;
        rand bit [7:0] data;
    endclass
    always_ff @(posedge clk) begin
        rand_class r;
        r = new();
        r.data       = $urandom;
        random_value <= r.data;
    end
endmodule
module specify_demo (
    input  wire a,
    output wire b
);
    specify
        specparam delay_val = 1;
        (a => b) = delay_val;
    endspecify
    assign b = a;
endmodule
module implicit_port_merge (
    input  wire        foo_in,
    output logic [3:0] out
);
    logic foo_internal;
    always_comb begin
        foo_internal = foo_in;
        out          = {3'b000, foo_internal};
    end
endmodule
