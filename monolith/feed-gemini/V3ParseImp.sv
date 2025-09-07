`line 100 "preproc_test_file.sv" 0
`timescale 1ns/1ps
interface BasePhysicalInterface;
    logic some_interface_signal;
endinterface
class MyParameterizedClass #(parameter int C_SIZE = 1);
    int m_data;
    function new(int d = 0);
        this.m_data = d;
    endfunction
endclass
class RandConstraintContainer;
    rand int rand_var_dist;
    rand int m_x;
    constraint c_dist {
        this.rand_var_dist dist {1 := 10, 2 := 20};
    };
    constraint c_complex { this.m_x > 0; };
    function void do_randomize_with_paren_like(input int limit);
        void'(this.randomize() with { this.m_x < limit; });
    endfunction
    function void do_randomize_with_bra_like(input int arr_idx);
        int my_internal_array[4];
        foreach (my_internal_array[i]) begin
            my_internal_array[i] = i;
        end
        void'(this.randomize() with { my_internal_array[arr_idx % 4] == 0; });
    endfunction
    function void do_randomize_with_cur(input logic flag_cond);
        void'(this.randomize() with { this.m_x == 10; if (flag_cond) this.m_x < 5; });
    endfunction
endclass
class RandomizeCaller;
    rand int my_rand_val;
    function void call_randomize();
        void'(this.randomize());
    endfunction
endclass
class MyScopedClass;
    static int static_member = 20;
    function int get_static(); return static_member; endfunction
endclass
class StaticMemberTest;
    static int static_prop_val = 30;
    static constraint my_static_constraint_block { static_prop_val > 0; }
endclass
class LocalScopeTest;
    local static int local_static_member = 50;
    static function int get_local_static_value(); return local_static_member; endfunction
    function int get_local_scoped(); return LocalScopeTest::local_static_member; endfunction
endclass
class TestClassNew;
    int value;
    function new(int v = 0); this.value = v; endfunction
endclass
module PreprocessorAndPragmas (
    input logic [7:0] data_in,
    output logic [7:0] data_out
);
    timeunit 1ps;
    timeprecision 1fs;
    localparam real TIME_VAL_MS = 100.5ms;
    localparam real TIME_VAL_US = 25.0us;
    localparam real TIME_VAL_PS = 1000ps;
    localparam real TIME_VAL_FS = 1000.0fs;
    localparam real TIME_VAL_S = 1s;
    assign data_out = data_in;
    `line 200 "preproc_test_file.sv" 1
endmodule
module SubComponent #(parameter int SUB_WIDTH = 1) (
    input logic [SUB_WIDTH-1:0] sub_in,
    output logic [SUB_WIDTH-1:0] sub_out
);
    assign sub_out = sub_in;
endmodule
module ParameterizedStructures (
    input logic [15:0] control_bus,
    output logic [31:0] result_bus
);
    typedef struct packed {
        logic [7:0] byte_field;
        logic [SIZE-1:0] sized_field;
    } MyParameterizedStruct_t #(int SIZE = 8);
    MyParameterizedClass #(8) class_instance;
    MyParameterizedStruct_t #(.SIZE(16)) struct_var;
    SubComponent #(.SUB_WIDTH(4)) inst_named_param (
        .sub_in(control_bus[3:0]),
        .sub_out(result_bus[3:0])
    );
    genvar j;
    logic [7:0] gen_sub_out[2];
    generate
        for (j = 0; j < 2; j++) begin : gen_inst_pos_param
            SubComponent #(8) inst_pos_param (
                .sub_in( j==0 ? control_bus[11:4] : {4'b0, control_bus[15:12]} ),
                .sub_out( gen_sub_out[j] )
            );
        end
    endgenerate
    assign result_bus[11:4] = gen_sub_out[0];
    assign result_bus[19:12] = gen_sub_out[1];
    logic [7:0] scoped_val;
    assign scoped_val = MyScopedClass::static_member;
    assign result_bus[31:20] = '0;
    always_comb begin
        class_instance = new(1);
        struct_var.byte_field = 8'hAA;
        struct_var.sized_field = '0;
    end
endmodule
module AdvancedLanguageFeatures (
    input logic [7:0] enable_flags,
    output logic [7:0] output_flags,
    output logic drive_strength_port
);
    typedef enum {RED, GREEN, BLUE} Color_t;
    typedef enum {CIRCLE, SQUARE} Shape_t;
    logic type_equal;
    assign type_equal = (type(Color_t) == type(Shape_t));
    assign output_flags[0] = type_equal;
    logic type_not_equal;
    assign type_not_equal = (type(Color_t) != type(Color_t));
    assign output_flags[1] = type_not_equal;
    TestClassNew obj1, obj2;
    always_comb begin
        obj1 = new();
        obj2 = TestClassNew::new(enable_flags[7:0]);
    end
    assign (supply0, supply1) drive_strength_port = enable_flags[2];
    const int MY_CONST_INT_ETC = 10;
    assign output_flags[3] = MY_CONST_INT_ETC;
    LocalScopeTest local_obj;
    always_comb begin
        local_obj = new();
        void'(local_obj.get_local_scoped());
        output_flags[4] = LocalScopeTest::get_local_static_value();
    end
    StaticMemberTest static_test_instance;
    assign output_flags[5] = StaticMemberTest::static_prop_val;
    MyParameterizedClass #(1) virtual_class_handle; 
    virtual BasePhysicalInterface virtual_if_handle;
    always_comb begin
        if (enable_flags[0]) begin
            virtual_class_handle = null;
            virtual_if_handle = null;
        end
    end
    always_comb begin
        automatic int sum = 0;
        automatic int my_array_for_with[4];
        my_array_for_with = '{0,1,2,3};
        foreach (my_array_for_with[idx]) begin
            sum += my_array_for_with[idx];
        end
        output_flags[6] = sum;
    end
    RandConstraintContainer rand_container_inst;
    always_comb begin
        rand_container_inst = new();
        void'(rand_container_inst.randomize());
        rand_container_inst.do_randomize_with_paren_like(100);
        rand_container_inst.do_randomize_with_bra_like(enable_flags[0]);
        rand_container_inst.do_randomize_with_cur(enable_flags[1]);
        output_flags[2] = rand_container_inst.m_x;
    end
    always_comb begin : my_begin_block
        output_flags[7] = enable_flags[7];
    end
    function automatic int dummy_return_one(); return 1; endfunction
    initial begin
        if (enable_flags[7]) begin
            fork : my_fork_label
                void'(dummy_return_one());
            join
        end
    end
    mailbox my_mbox;
    process my_proc;
    semaphore my_sema;
    int std_as_id;
    assign std_as_id = enable_flags[0];
    logic PATHPULSE__024_dummy_id; 
    assign PATHPULSE__024_dummy_id = enable_flags[0];
    logic enable_flag_bit7; 
    always_comb begin
        enable_flag_bit7 = enable_flags[7];
    end
    logic cg_sampling_trigger;
    covergroup my_covergroup @(posedge cg_sampling_trigger);
        option.per_instance = 1;
        coverpoint enable_flags[1];
        coverpoint enable_flags[0] { bins zero = {0} with (enable_flag_bit7 == 0); }
    endgroup
    always_comb begin
        static my_covergroup cov_inst = new();
        cg_sampling_trigger = enable_flags[0];
    end
endmodule
module RandomizeUsage (
    input logic r_in,
    output logic r_out
);
    RandomizeCaller rand_caller_inst;
    always_comb begin
        rand_caller_inst = new();
        rand_caller_inst.call_randomize();
        r_out = r_in;
    end
endmodule
module GlobalClockingContainer (
    input logic clk_in,
    output logic clk_out
);
    logic internal_global_clk_sig;
    assign internal_global_clk_sig = clk_in;
    global clocking my_top_cb @(posedge internal_global_clk_sig);
    endclocking
    assign clk_out = internal_global_clk_sig;
endmodule
module CommentTarget (
    input logic in_bit,
    output logic out_bit
);
    /*verilator lint_save*/
    /*verilator lint_off UNUSED*/
    logic dummy_unused_signal; 
    assign out_bit = in_bit;
    /*verilator lint_restore*/
    /*verilator tag MY_TEST_TAG*/
    /*verilator bad_pragma_example*/ 
endmodule
`line 300 "post_module_file.sv" 2
