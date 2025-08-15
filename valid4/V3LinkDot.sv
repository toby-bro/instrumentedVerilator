`default_nettype wire
typedef struct packed {
    logic [3:0] field1;
    logic [3:0] field2;
} my_struct_t;
interface BasicInterface (
    input logic clk,
    output logic rst_n,
    inout logic [WIDTH-1:0] data
);
    parameter int WIDTH = 4;
    modport Master (
        input clk,
        output rst_n,
        input data
    );
    modport Slave (
        input clk,
        input rst_n,
        output data
    );
    function automatic int get_data_value(logic [WIDTH-1:0] input_data_arg);
        return input_data_arg;
    endfunction
endinterface
module ModHierarchy (
    input logic [7:0] in_data_h,
    output logic [7:0] out_data_h
);
    logic [7:0] internal_var_h;
    always_comb begin : named_block
        logic [7:0] local_var;
        local_var = in_data_h + 1;
        internal_var_h = local_var;
        begin : unnamed_block
            logic [7:0] temp_unnamed_var;
            temp_unnamed_var = internal_var_h + 2;
            out_data_h = temp_unnamed_var;
        end
    end
    assign internal_var_h = named_block.local_var;
endmodule
module ModInterfaces (
    input logic sys_clk,
    output logic sys_rst_n,
    input logic [3:0] input_data_i
);
    BasicInterface if_master_inst (
        .clk(sys_clk),
        .rst_n(sys_rst_n),
        .data(input_data_i)
    );
    BasicInterface if_slave_inst ();
    assign if_slave_inst.clk = sys_clk;
    assign if_slave_inst.rst_n = sys_rst_n;
    assign if_slave_inst.data = if_master_inst.data + 1;
    logic [3:0] func_val;
    always_comb begin : logic_block
        func_val = if_master_inst.get_data_value(if_master_inst.data);
        sys_rst_n = (func_val == 4'd0);
    end
    input logic sys_in;
    output logic sys_out;
    assign sys_out = sys_in;
endmodule
module ModDefparam (
    input logic clk_dp,
    output logic rst_dp
);
    BasicInterface if_dp_inst ();
    defparam if_dp_inst.WIDTH = 8;
    assign if_dp_inst.clk = clk_dp;
    assign rst_dp = if_dp_inst.rst_n;
    logic [if_dp_inst.WIDTH-1:0] output_data_dp;
    assign output_data_dp = if_dp_inst.data;
endmodule
class BaseClass;
    localparam int BASE_VAL = 10;
    rand int base_rand_val;
    function new();
        base_rand_val = 0;
    endfunction
    virtual function int get_value();
        return base_rand_val + BASE_VAL;
    endfunction
    static function int get_static_value(int input_val);
        return input_val * 2;
    endfunction
endclass
class DerivedClass extends BaseClass;
    rand int derived_rand_val;
    function new();
        super.new();
        derived_rand_val = 5;
    endfunction
    virtual function int get_value();
        return super.get_value() + derived_rand_val;
    endfunction
    constraint derived_constraint {
        derived_rand_val inside {[1:10]};
    }
endclass
interface class IPrintable;
    pure virtual function void print_info();
endinterface
class MyClass implements IPrintable;
    int a;
    function new(int init_a);
        this.a = init_a;
    endfunction
    virtual function void print_info();
    endfunction
endclass
module ModClasses (
    input logic clk_c,
    output logic out_flag_c
);
    DerivedClass dc_inst;
    MyClass mc_inst;
    int static_result;
    always_comb begin : class_inst_block
        dc_inst = new();
        void'(dc_inst.randomize());
        static_result = BaseClass::get_static_value(10);
        out_flag_c = (static_result > 0);
        mc_inst = new(5);
    end
    logic [1:0] module_internal_var_m4;
    always_comb begin : inner_block
        logic [1:0] inner_block_local_var;
        inner_block_local_var = clk_c ? 2'b11 : 2'b00;
        out_flag_c = (inner_block_local_var == 2'b11);
    end
endmodule
module ParamTypeModule #(
    parameter type T = logic
)(
    input T in_arg,
    output T out_arg
);
    assign out_arg = in_arg;
endmodule
typedef enum {RED, GREEN, BLUE} Color_t;
module ModParamsTypedefs (
    input logic in_trigger_p,
    output logic [3:0] out_val_p
);
    parameter int GLOBAL_WIDTH = 16;
    localparam int LOCAL_OFFSET = 4;
    Color_t current_color;
    my_struct_t s_inst;
    my_struct_t assigned_struct;
    logic [GLOBAL_WIDTH-1:0] wide_data;
    always_comb begin
        current_color = in_trigger_p ? GREEN : RED;
        wide_data = GLOBAL_WIDTH + LOCAL_OFFSET;
        out_val_p = wide_data[3:0];
    end
endmodule
class Randomizer;
    rand int rand_val;
    constraint c_val { rand_val > 5; };
endclass
module ModAdvancedControl (
    input logic [7:0] data_ac,
    input logic clk_ac,
    output logic [7:0] out_sum_ac
);
    logic [7:0] array_data [0:3];
    logic [7:0] sum;
    Randomizer my_randomizer;
    clocking my_cb @(posedge clk_ac);
        input data_ac;
        output out_sum_ac;
        inout sum;
    endclocking
    always_comb begin
        my_randomizer = new();
        void'(my_randomizer.randomize() with { my_randomizer.rand_val == int'(data_ac) });
        sum = 0;
        foreach (array_data[i]) begin
            array_data[i] = data_ac + i;
            sum = sum + array_data[i];
        end
        out_sum_ac = sum;
    end
endmodule
module ModDPI (
    input int dpi_in,
    output int dpi_out
);
    export "DPI-C" function my_dpi_function;
    function int my_dpi_function(int arg);
        return arg * 2;
    endfunction
    assign dpi_out = my_dpi_function(dpi_in);
endmodule
package MyPackage;
    logic [15:0] pkg_data = 16'hAAAA;
    function int get_pkg_data();
        return pkg_data;
    endfunction
    localparam int PKG_VERSION = 1;
endpackage
package MyOtherPackage;
    export MyPackage::*;
    export MyPackage::get_pkg_data;
endpackage
module ModPackages (
    input logic trigger_pkg,
    output logic [15:0] out_pkg
);
    import MyPackage::pkg_data;
    import MyOtherPackage::*;
    logic [15:0] temp_pkg_data;
    always_comb begin
        temp_pkg_data = pkg_data;
        out_pkg = get_pkg_data() + PKG_VERSION;
    end
endmodule
module ModImplicitVar (
    input logic in_imp,
    output logic out_imp
);
    assign undeclared_signal = in_imp;
    assign another_signal = undeclared_signal;
    logic [0:0] module_level_var;
    always_comb begin : block_a
        logic [0:0] var_in_block_a;
        logic [0:0] module_level_var;
        var_in_block_a = in_imp;
        module_level_var = in_imp & var_in_block_a;
        out_imp = undeclared_signal || another_signal || module_level_var;
    end
endmodule
module ModPorts (
    input clk_p,
    output rst_p,
    inout data_p,
    input logic new_port_input_conn,
    output logic new_port_output_conn
);
    input logic ansi_in;
    output logic ansi_out;
    inout logic ansi_inout;
    assign ansi_out = ansi_in;
    assign ansi_inout = ansi_in;
    assign rst_p = 1'b0;
    assign data_p = 1'b0;
    logic [0:0] my_local_var;
    always_comb begin : some_logic_block
        my_local_var = ansi_in;
        begin : inner_scope_for_shadowing
            logic [0:0] my_local_var;
            my_local_var = ansi_inout;
        end
    end
    assign new_port_output_conn = new_port_input_conn;
endmodule
module ModHierarchicalDot (
    input logic [3:0] in_hdot,
    output logic [3:0] out_hdot
);
    genvar i;
    generate
        for (i = 0; i < 2; i++) begin : gen_loop
            logic [3:0] gen_local_var;
            assign gen_local_var = in_hdot + i;
            always_comb begin : nested_block
                logic [3:0] nested_local_var;
                nested_local_var = gen_local_var * 2;
                out_hdot = nested_local_var;
                assign out_hdot = gen_loop[0].nested_block.nested_local_var;
            end
        end
    endgenerate
    function automatic logic [3:0] get_valid_hierarchical_data();
        logic [3:0] temp_val = gen_loop[0].gen_local_var; 
        return temp_val;
    endfunction
    assign out_hdot = get_valid_hierarchical_data();
endmodule
class GenericClass #(parameter type T = int);
    T generic_data;
    function new(T init_data);
        generic_data = init_data;
    endfunction
    virtual function T get_generic_data();
        return generic_data;
    endfunction
endclass
class SpecificClass extends GenericClass #(int);
    rand int specific_rand_val;
    function new(int init_data);
        super.new(init_data);
        specific_rand_val = 1;
    endfunction
    constraint specific_c { specific_rand_val inside {1, 2, 3}; }
endclass
class AnotherSpecificClass extends GenericClass #(string);
    string another_data;
    function new(string s);
        super.new(s);
        another_data = s;
    endfunction
endclass
module ModComplexClasses (
    input logic clk_cc,
    output logic [7:0] out_cc
);
    SpecificClass sc_inst;
    AnotherSpecificClass asc_inst;
    always_comb begin : class_test_block
        string temp_str;
        sc_inst = new(10);
        void'(sc_inst.randomize());
        asc_inst = new("hello");
        temp_str = asc_inst.get_generic_data();
        out_cc = sc_inst.get_generic_data();
    end
endmodule
package DotTestPkg;
    int pkg_var = 100;
    function int pkg_func(int arg);
        return arg + 1;
    endfunction
    class PkgInnerClass;
        int inner_var = 10;
        static function int get_static_inner();
            return 20;
        endfunction
    endclass
endpackage
module ModDottedReferences (
    input logic [7:0] in_dotref,
    output logic [7:0] out_dotref
);
    logic local_var_dr = 8'hFF;
    import DotTestPkg::pkg_var;
    logic [7:0] temp_val_pkg_var;
    logic [7:0] temp_val_pkg_func;
    assign temp_val_pkg_var = DotTestPkg::pkg_var + in_dotref;
    assign temp_val_pkg_func = DotTestPkg::pkg_func(in_dotref);
    DotTestPkg::PkgInnerClass inner_inst;
    my_struct_t s_inst;
    my_struct_t assigned_struct;
    typedef enum {VAL_A, VAL_B, VAL_C} MyEnum_t;
    MyEnum_t enum_val;
    logic [1:0] pat_member_ctrl;
    logic [7:0] packed_array_var;
    always_comb begin : dot_block
        inner_inst = new(); 
        logic [7:0] temp_inner_var = '0; 
        logic [7:0] temp_static_inner = '0;
        temp_inner_var = inner_inst.inner_var;
        temp_static_inner = DotTestPkg::PkgInnerClass::get_static_inner();
        out_dotref = temp_inner_var + temp_static_inner + temp_val_pkg_var + temp_val_pkg_func;
        case(pat_member_ctrl)
            2'b00: enum_val = MyEnum_t.VAL_A;
            2'b01: enum_val = MyEnum_t.VAL_B;
            default: enum_val = MyEnum_t.VAL_C;
        endcase
        assigned_struct = '{field1: in_dotref[3:0], field2: 4'hF};
    end
    assign s_inst.field1 = in_dotref[3:0];
    logic [7:0] temp_struct_field;
    assign temp_struct_field = s_inst.field2;
    assign packed_array_var[3:0] = in_dotref;
    assign packed_array_var[6:4] = in_dotref[2:0];
    logic [7:0] temp_packed_array;
    assign temp_packed_array = packed_array_var;
    logic [7:0] temp_enum_out;
    assign temp_enum_out = {enum_val, in_dotref[3:0]};
endmodule
module ModClockingDetails (
    input logic sys_clk_cd,
    input logic data_in_cd,
    output logic data_out_cd
);
    clocking global_cb @(posedge sys_clk_cd);
        input data_in_cd;
    endclocking
    clocking my_named_cb @(posedge sys_clk_cd);
        output data_out_cd;
        input internal_clkvar_in;
        output internal_clkvar_out;
    endclocking
    logic internal_clkvar_in_signal;
    logic internal_clkvar_out_signal;
    assign my_named_cb.internal_clkvar_in = internal_clkvar_in_signal;
    assign internal_clkvar_out_signal = my_named_cb.internal_clkvar_out;
    always_ff @(posedge sys_clk_cd or negedge data_in_cd) begin
        data_out_cd <= data_in_cd;
    end
    assign data_out_cd = internal_clkvar_in_signal;
endmodule
