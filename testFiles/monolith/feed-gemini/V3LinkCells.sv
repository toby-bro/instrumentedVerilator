module InnerModule (
    input logic in_a,
    input logic in_b,
    output logic out_c,
    output logic out_d,
    input logic in_e = 1'b1
);
    assign out_c = in_a ^ in_b;
    assign out_d = in_a & in_b;
endmodule
module ParamModule #(
    parameter int P_WIDTH = 8,
    parameter int P_DEFAULT = 10
) (
    input logic [P_WIDTH-1:0] in_val,
    output logic [P_WIDTH-1:0] out_val
);
    assign out_val = in_val + P_DEFAULT;
endmodule
module InternalDotStarModule (
    input logic [7:0] in_data,
    output logic [7:0] out_data
);
    assign out_data = in_data + 1;
endmodule
module MixedPortModule (
    input logic mix_in_1,
    input logic mix_in_2,
    output logic mix_out_1,
    output logic mix_out_2
);
    assign mix_out_1 = mix_in_1;
    assign mix_out_2 = mix_in_2;
endmodule
module ModuleInstantiationVariants (
    input logic [7:0] in_data,
    output logic [7:0] out_data
);
    logic [7:0] internal_wire1;
    logic [7:0] internal_wire2;
    logic internal_logic_a;
    logic internal_logic_b;
    logic internal_logic_c_pos;
    logic internal_logic_d_pos;
    logic internal_logic_c_named;
    logic internal_logic_d_named;
    logic [7:0] dot_star_output;
    InnerModule inst_pos (
        internal_logic_a,
        internal_logic_b,
        internal_logic_c_pos,
        internal_logic_d_pos
    );
    InnerModule inst_named (
        .in_a(internal_logic_a),
        .out_d(internal_logic_d_named),
        .in_b(internal_logic_b),
        .out_c(internal_logic_c_named)
    );
    InternalDotStarModule inst_dot_star (
        .in_data(in_data),
        .out_data(dot_star_output)
    );
    ParamModule #(.P_WIDTH(8), .P_DEFAULT(20)) inst_param (
        .in_val(in_data),
        .out_val(out_data)
    );
    ParamModule inst_param_default (
        .in_val(internal_wire1),
        .out_val(internal_wire2)
    );
    assign internal_wire1 = in_data + 1;
    assign internal_logic_a = internal_wire1[0];
    assign internal_logic_b = internal_wire1[1];
endmodule
module RecursiveModule #(parameter int RECURSION_DEPTH = 3) (
    input logic [7:0] in_val,
    output logic [7:0] out_val
);
    wire [7:0] next_val;
    generate
        if (RECURSION_DEPTH == 0) begin : base_case
            assign out_val = 8'h0;
        end else begin : recursive_case
            RecursiveModule #(.RECURSION_DEPTH(RECURSION_DEPTH - 1)) rec_inst (
                .in_val(in_val - 1),
                .out_val(next_val)
            );
            assign out_val = next_val + 1;
        end
    endgenerate
endmodule
interface axi_lite_if (input bit clk);
    logic        arvalid;
    logic        arready;
    logic [31:0] araddr;
    logic        rvalid;
    logic        rready;
    logic [31:0] rdata;
    logic        req_in;
    logic        ack_out;
    modport master (
        output arvalid, araddr,
        input  arready, rdata, rvalid,
        input  clk,
        output req_in,
        input  ack_out
    );
    modport slave (
        input  arvalid, araddr,
        output arready, rdata, rvalid,
        input  clk,
        input  req_in,
        output ack_out
    );
endinterface
module InterfaceUserModule (
    input logic clk,
    input logic req,
    output logic ack
);
    axi_lite_if  axi_if_inst (clk);
    always @(posedge clk) begin
        axi_if_inst.req_in <= req;
        axi_if_inst.arvalid <= req;
        axi_if_inst.araddr <= 32'h100;
        axi_if_inst.rready <= 1;
        axi_if_inst.ack_out <= req;
    end
    assign ack = axi_if_inst.ack_out;
    virtual axi_lite_if virtual_axi_if;
    class MyLocalClass;
        int dummy_val;
        function new(); dummy_val = 0; endfunction
    endclass
    MyLocalClass my_local_obj;
    always_comb begin
        my_local_obj = new();
    end
endmodule
package my_package;
    parameter int PKG_PARAM = 5;
    typedef enum {RED, GREEN, BLUE} color_t;
    function int add_one(int val);
        return val + 1;
    endfunction
endpackage
package another_package;
    import my_package::*;;
    import my_package::color_t;
    export my_package::add_one;
    export my_package::PKG_PARAM;
    typedef struct packed {
        logic [7:0] addr;
        logic [31:0] data;
    } my_struct_t;
    function automatic int get_pkg_param();
        return my_package::PKG_PARAM;
    endfunction
endpackage
module PackageUserModule (
    input int in_val,
    output int out_val
);
    import my_package::*; ;
    import another_package::my_struct_t;
    color_t current_color;
    my_struct_t current_struct;
    assign current_color = GREEN;
    assign current_struct.addr = in_val[7:0];
    assign current_struct.data = in_val;
    assign out_val = add_one(in_val) + another_package::get_pkg_param();
    class PackageClass;
        int m_data;
        function new(int data);
            m_data = data;
        endfunction
        function int get_data();
            return m_data;
        endfunction
    endclass
    PackageClass pkg_object;
    logic [31:0] dummy_class_output;
    always_comb begin
        pkg_object = new(in_val);
        dummy_class_output = (pkg_object == null) ? 0 : pkg_object.get_data();
    end
endmodule
class BaseClass #(parameter int BASE_OFFSET = 10);
    int value;
    function new(int v);
        value = v + BASE_OFFSET;
    endfunction
    virtual function int get_value();
        return value;
    endfunction
endclass
class DerivedClass #(parameter int DERIVED_FACTOR = 2) extends BaseClass #(DERIVED_FACTOR + 5);
    function new(int v);
        super.new(v);
        value = value * DERIVED_FACTOR;
    endfunction
    function int get_derived_value();
        return get_value();
    endfunction
endclass
module ClassUserModule (
    input int in_param_val,
    output int out_calc_val
);
    DerivedClass my_derived_object;
    always_comb begin
        my_derived_object = new(in_param_val);
        out_calc_val = (my_derived_object == null) ? 0 : my_derived_object.get_derived_value();
    end
endmodule
module TargetForBind (
    input logic in_a,
    output logic out_b
);
    assign out_b = ~in_a;
endmodule
module BoundModule (
    input logic bound_in,
    output logic bound_out
);
    assign bound_out = bound_in;
endmodule
config MyConfig;
    design TestLib;
    instance TestLib.module_name use TargetForBind;
    cell A.B use TestLib.TargetForBind;
endconfig
module UnsupportedFeaturesModule (
    input logic in_trigger,
    output logic out_status
);
    logic internal_sig;
    TargetForBind inst_target (.in_a(in_trigger), .out_b(internal_sig));
    bind TargetForBind : inst_target BoundModule bind_inst (.bound_in(in_trigger), .bound_out(out_status));
    assign out_status = internal_sig;
endmodule
module InnerModuleForWarnings (
    input logic in_req,
    output logic out_ack,
    input logic [7:0] data_in,
    input logic [7:0] optional_data_in = 8'hFF
);
    assign out_ack = in_req;
endmodule
module VariableTypesAndPortWarnings (
    input logic [3:0] input_flags,
    output logic [3:0] output_status
);
    logic               my_logic_var;
    bit                 my_bit_var;
    int                 my_int_var;
    byte                my_byte_var;
    shortint            my_shortint_var;
    longint             my_longint_var;
    integer             my_integer_var;
    time                my_time_var;
    real                my_real_var;
    realtime            my_realtime_var;
    event               my_event_var;
    enum {STATE_IDLE, STATE_BUSY} my_enum_var;
    struct packed {
        logic [1:0] id;
        logic [7:0] val;
    } my_struct_var;
    union packed {
        logic [15:0] word;
        logic [1:0][7:0]  byte_array;
    } my_union_var;
    logic [7:0] my_array_var [4];
    logic [7:0] my_dyn_array_var [];
    logic initial_value_var = 1'b0;
    parameter int MY_PARAMETER = 100;
    localparam int MY_LOCALPARAM = 200;
    logic req_internal;
    logic ack_internal_1;
    logic ack_internal_2;
    logic [7:0] data_internal;
    logic mixed_in_1, mixed_in_2, mixed_out_1, mixed_out_2;
    InnerModuleForWarnings inst_warn_empty_named (
        .in_req(req_internal),
        .out_ack(ack_internal_1),
        .data_in(),
        .optional_data_in()
    );
    InnerModuleForWarnings inst_warn_missing_port (
        .in_req(req_internal),
        .out_ack(ack_internal_2),
        .data_in(data_internal)
    );
    MixedPortModule inst_warn_mixed (
        .mix_in_1(mixed_in_1),
        .mix_in_2(mixed_in_2),
        .mix_out_1(mixed_out_1),
        .mix_out_2(mixed_out_2)
    );
    assign my_logic_var = input_flags[0];
    assign my_bit_var = input_flags[1];
    assign my_int_var = input_flags[2];
    assign my_byte_var = input_flags[3];
    assign my_struct_var.id = input_flags[1:0];
    assign my_struct_var.val = {4'h0, input_flags};
    assign my_union_var.word = {8'h0, input_flags, 4'h0, 4'h0};
    assign req_internal = input_flags[0];
    assign data_internal = {4'h0, input_flags};
    assign output_status[0] = ack_internal_1;
    assign output_status[1] = my_logic_var;
    assign output_status[2] = (MY_PARAMETER > 0) ? 1'b1 : 1'b0;
    assign output_status[3] = (MY_LOCALPARAM > 0) ? 1'b1 : 1'b0;
endmodule
module CyclicModuleB #(parameter int CURRENT_DEPTH = 1) (
    input logic dummy_in,
    output logic out_result
);
    logic next_result;
    generate
        if (CURRENT_DEPTH == 0) begin : base_case
            assign out_result = 1'b0;
        end else begin : recursive_case
            CyclicModuleA #(.CURRENT_DEPTH(CURRENT_DEPTH - 1)) inst_a (
                .dummy_in(dummy_in),
                .out_result(next_result)
            );
            assign out_result = next_result;
        end
    endgenerate
endmodule
module CyclicModuleA #(parameter int CURRENT_DEPTH = 1) (
    input logic dummy_in,
    output logic out_result
);
    logic next_result;
    generate
        if (CURRENT_DEPTH == 0) begin : base_case
            assign out_result = 1'b1;
        end else begin : recursive_case
            CyclicModuleB #(.CURRENT_DEPTH(CURRENT_DEPTH - 1)) inst_b (
                .dummy_in(dummy_in),
                .out_result(next_result)
            );
            assign out_result = next_result;
        end
    endgenerate
endmodule
module CyclicInstantiationModule (
    input logic enable_cycle,
    output logic final_result
);
    CyclicModuleA #(.CURRENT_DEPTH(2)) inst_initial (
        .dummy_in(enable_cycle),
        .out_result(final_result)
    );
endmodule
