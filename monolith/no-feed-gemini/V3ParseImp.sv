module Module_StdKeywords (
    input bit clk_i,
    output logic [7:0] data_o
);
    class MyClass;
        rand int val;
        function new();
            val = 0;
        endfunction
        function void set_val(int v);
            val = v;
        endfunction
    endclass
    MyClass my_instance;
    process my_process_handle;
    mailbox #(int) my_mailbox = new(1);
    semaphore my_semaphore = new(1);
    always_comb begin
        my_instance = new();
        if (clk_i) begin
            void'(my_instance.randomize() with { val > 10; });
            my_instance.set_val(std::max(my_instance.val, 5));
            void'(my_mailbox.try_put(my_instance.val));
            void'(my_semaphore.try_get());
        end else begin
            void'(my_semaphore.try_put());
        end
        data_o = my_instance.val;
    end
endmodule
module Module_LineDirective (
    input bit [3:0] in_a,
    output logic [3:0] out_b
);
    localparam int MY_PARAM = 10;
`line 100 "new_file_1.sv" 1
    localparam int ANOTHER_PARAM = 20;
    logic [3:0] temp_val1;
    assign temp_val1 = in_a + ANOTHER_PARAM;
`line 200 "new_file_2.sv"
    logic [3:0] temp_val2;
    assign temp_val2 = in_a * 2;
`line 100 "new_file_1.sv" 2
    logic [3:0] temp_val3;
    assign temp_val3 = in_a + MY_PARAM;
`line 1 "original_file.sv" 2
    assign out_b = in_a + MY_PARAM;
endmodule
`timescale 1ns / 100ps
module Module_Timescale (
    input logic [15:0] in_data,
    output logic [15:0] out_data
);
    timeunit 1ps;
    timeprecision 1fs;
    parameter TIME_CONST_NS = 10ns;
    parameter TIME_CONST_MS = 5ms;
    parameter TIME_CONST_US = 25us;
    parameter TIME_CONST_PS = 100ps;
    parameter TIME_CONST_FS = 500fs;
    parameter REAL_TIME_VAL = 1.2345s;
    assign out_data = in_data;
endmodule
module Module_VerilatorLint (
    input bit flag_i,
    output logic [1:0] state_o
);
    /* verilator lint_off UNUSED */
    logic unused_signal;
    /* verilator lint_on UNUSED */
    /* verilator lint_save */
    /* verilator lint_off WIDTH */
    assign state_o = flag_i ? 2'b01 : 1'b0;
    /* verilator lint_restore */
    logic [3:0] wider_signal = 1'b0;
    assign state_o[0] = wider_signal[0];
    /* verilator tag MY_TEST_TAG */
    /* verilator bad_pragma */
endmodule
module Module_UndefinedMacro (
    input bit [7:0] in_val,
    output logic [7:0] out_val
);
    `ifdef UNKNOWN_MACRO_TO_VERIFY_ERROR_PATH
        assign out_val = in_val + 1;
    `else
        assign out_val = in_val - 1;
    `endif
endmodule
module Module_TimeLiterals (
    input logic enable_i,
    output logic [31:0] result_o
);
    parameter longreal DELAY_S  = 1.0s;
    parameter longreal DELAY_MS = 100.5ms;
    parameter longreal DELAY_US = 50.0us;
    parameter longreal DELAY_NS = 2.5ns;
    parameter longreal DELAY_PS = 10ps;
    parameter longreal DELAY_FS = 200fs;
    always_comb begin
        if (enable_i) begin
            result_o = $rtoi(DELAY_S + DELAY_MS + DELAY_US + DELAY_NS + DELAY_PS + DELAY_FS);
        end else begin
            result_o = 0;
        end
    end
endmodule
module my_sub_module #(
    parameter int DATA_WIDTH = 8
) (
    input logic [DATA_WIDTH-1:0] in,
    output logic [DATA_WIDTH-1:0] out
);
    assign out = in;
endmodule
module Module_InstanceParsing (
    input logic [7:0] input_vec,
    output logic [7:0] output_vec
);
    my_sub_module #(.DATA_WIDTH(8)) inst_single (.in(input_vec), .out(output_vec));
    my_sub_module #(.DATA_WIDTH(4)) inst_array[1:0] (
        .in({input_vec[3:0], input_vec[7:4]}),
        .out({output_vec[3:0], output_vec[7:4]})
    );
endmodule
module Module_TypeParsing (
    input bit trigger_i,
    output logic [15:0] calculated_o
);
    typedef struct packed {
        logic [7:0] field1;
        logic [7:0] field2;
    } my_packed_struct_t;
    typedef class MyParamClass #(parameter int SIZE = 1);
        int value[SIZE];
        function new();
            foreach (value[i]) value[i] = i;
        endfunction
    endclass
    MyParamClass#(4) my_class_inst_1;
    MyParamClass#() my_class_inst_2;
    my_packed_struct_t my_struct_var;
    my_packed_struct_t my_struct_array[2];
    always_comb begin
        my_class_inst_1 = new();
        my_class_inst_2 = new();
        my_struct_var = '{field1: 8'hAA, field2: 8'hBB};
        my_struct_array = '{'{8'h11, 8'h22}, '{8'h33, 8'h44}};
        if (trigger_i) begin
            calculated_o = my_struct_var.field1 + my_struct_array[0].field2 + my_class_inst_1.value[0];
        end else begin
            calculated_o = my_struct_var.field2 + my_struct_array[1].field1 + my_class_inst_2.value[0];
        end
    end
endmodule
module Module_ArrayParsing (
    input logic [7:0] in_data_array [3:0],
    output logic [7:0] out_data
);
    logic [7:0] packed_2d_array [4:0][7:0];
    logic unpacked_2d_array [2:0][1:0];
    logic [1:0] mixed_array [5:0] [6:0];
    always_comb begin
        out_data = 0;
        for (int i=0; i<4; i++) begin
            out_data = out_data + in_data_array[i];
        end
        packed_2d_array[0][0] = out_data;
        unpacked_2d_array[0][0] = packed_2d_array[0][0][0];
        mixed_array[0][0] = 2'b00;
    end
endmodule
module Module_TypeEquality (
    input bit select_type,
    output logic match_o
);
    typedef enum {STATE_IDLE, STATE_RUNNING} State_t;
    typedef logic [7:0] Byte_t;
    always_comb begin
        match_o = 0;
        if (select_type) begin
            if (type(State_t) == type(logic [1:0])) begin
                match_o = 1;
            end
        end else begin
            if (type(Byte_t) === type(logic [7:0])) begin
                match_o = 1;
            end
        end
    end
endmodule
module Module_ClassNew (
    input bit trigger_new,
    output logic [7:0] val_o
);
    class MySimpleClass;
        int data_val;
        function new();
            data_val = 10;
        endfunction
        function new(int init_val);
            data_val = init_val;
        endfunction
    endclass
    MySimpleClass my_object;
    MySimpleClass another_object;
    always_comb begin
        val_o = 0;
        if (trigger_new) begin
            my_object = new();
            another_object = new(20);
            val_o = my_object.data_val + another_object.data_val;
        end else begin
            my_object = null;
            val_o = 0;
        end
    end
endmodule
package Package;
    parameter int PKG_PARAM = 100;
    function int pkg_func(int a);
        return a * PKG_PARAM;
    endfunction
endpackage
module Module_ComplexIDs (
    input bit [7:0] input_a,
    output logic [15:0] output_b
);
    int result_pkg_func;
    always_comb begin
        result_pkg_func = Package::pkg_func(input_a);
        output_b = result_pkg_func;
    end
    class AnotherClass;
        static int static_member = 50;
    endclass
    int static_val;
    always_comb begin
        static_val = AnotherClass::static_member;
        output_b += static_val;
    end
    logic [7:0] PATHPULSE__024_status;
    assign PATHPULSE__024_status = input_a;
    assign output_b += PATHPULSE__024_status;
endmodule
module Module_TokenPipeline (
    input bit clk_in,
    input bit rst_in,
    output logic [3:0] count_out
);
    logic [3:0] my_reg;
    wire (strong0, weak1) driven_wire;
    assign driven_wire = clk_in;
    assign my_reg[0] = driven_wire;
    always_ff @(posedge clk_in or posedge rst_in) begin : my_labeled_block
        if (rst_in) begin
            my_reg <= 0;
        end else begin
            my_reg <= my_reg + 1;
        end
    end
    function automatic void dummy_fork_logic();
        fork : my_fork_block
        join_none
    endfunction
    class ConstRefClass;
        int value_val;
        function new(int val);
            this.value_val = val;
        endfunction
    endclass
    class ConstRefProcessor;
        const ref ConstRefClass container_ref;
        function new(const ref ConstRefClass val_obj);
            this.container_ref = val_obj;
        endfunction
        function int get_val();
            return container_ref.value_val;
        endfunction
    endclass
    clocking global_cb @(posedge clk_in);
        input rst_in;
    endclocking
    class LocalClass;
        local int local_static_val = 100;
    endclass
    class NewTestClass;
        int val;
        function new(); val = 1; endfunction
    endclass
    NewTestClass new_obj;
    class StaticConstraintClass;
        rand int val_a;
        rand int val_b;
        static constraint my_constraint {
            val_a < val_b;
        }
        function new(); void'(randomize()); endfunction
    endclass
    StaticConstraintClass static_con_obj;
    virtual class VirtualBaseClass;
        pure virtual function int get_value();
    endclass
    virtual interface VirtualInterface;
        logic [7:0] data;
        modport TEST (input data);
    endinterface
    typedef int my_virtual_type_t;
    virtual my_virtual_type_t virtual_var;
    class WithRandomizeClass;
        rand int r_val;
        function new(); endfunction
    endclass
    WithRandomizeClass with_obj;
    int arr_with_cond[];
    int queue_with_cond[$];
    always_comb begin
        count_out = my_reg;
        dummy_fork_logic();
        ConstRefClass local_val_obj = new(5);
        ConstRefProcessor const_ref_obj = new(local_val_obj);
        count_out += const_ref_obj.get_val();
        new_obj = new();
        static_con_obj = new();
        with_obj = new();
        void'(with_obj.randomize() with { r_val > 10; });
        arr_with_cond = new[5];
        foreach (arr_with_cond[i]) arr_with_cond[i] = i * 2;
        arr_with_cond = arr_with_cond.find with (item > 5);
        queue_with_cond = {1,2,3,4,5,6};
        queue_with_cond = queue_with_cond.find with (item % 2 == 0);
    end
endmodule
module Module_GlobalKeyword (
    input bit enable,
    output logic [7:0] data_out
);
    clocking global_clocking_block @(posedge enable);
        output data_out;
    endclocking
    assign data_out = 8'hAB;
endmodule
module Module_ConstRefLocal (
    input bit [7:0] val_in,
    output logic [7:0] val_out
);
    class MyValueContainer;
        int m_value;
        local int m_local_value;
        function new(int v);
            m_value = v;
            m_local_value = v * 2;
        endfunction
        function int get_value();
            return m_value;
        endfunction
        function int get_local_value();
            return m_local_value;
        endfunction
    endclass
    class MyConstRefProcessor;
        const ref MyValueContainer container_ref;
        local MyValueContainer local_container;
        function new(const ref MyValueContainer ref_cont);
            this.container_ref = ref_cont;
            this.local_container = new(ref_cont.get_value() + 1);
        endfunction
        function int process_value();
            return container_ref.get_value() + local_container.get_local_value();
        endfunction
    endclass
    MyValueContainer my_container;
    MyConstRefProcessor my_processor;
    always_comb begin
        my_container = new(val_in);
        my_processor = new(my_container);
        val_out = my_processor.process_value();
    end
endmodule
