package my_global_pkg;
    import "DPI-C" function int c_add_one(int val);
    class PkgGlobalClass;
        int m_pkg_data;
        static int s_pkg_counter = 0;
        static task static_pkg_task();
            s_pkg_counter = c_add_one(s_pkg_counter);
        endtask
        function new(int data_val);
            m_pkg_data = data_val;
            s_pkg_counter++;
        endfunction
        function int get_pkg_data();
            return m_pkg_data;
        endfunction
        static function int get_pkg_counter();
            return s_pkg_counter;
        endfunction
    endclass
    typedef (* public *) packed struct {
        logic [7:0] field_a;
        logic [7:0] field_b;
    } PkgPackedStruct_t;
    covergroup PkgCoverGroup(logic [7:0] data_val, logic clk_for_cg) @(posedge clk_for_cg);
        option.per_instance = 1;
        coverpoint data_val {
            bins low = {0, 1};
            bins high = {[250:255]};
        }
    endgroup
endpackage
module ClassBasic (
    input logic [7:0] in_data,
    output logic [7:0] out_result
);
    class MySimpleClass;
        rand int m_value;
        int m_offset;
        function new(int offset_val);
            m_offset = offset_val;
        endfunction
        function int calculate(int input_val);
            return input_val + m_value + m_offset;
        endfunction
    endclass
    MySimpleClass instance_a;
    always_comb begin
        out_result = 8'h00;
        instance_a = new(10);
        void'(instance_a.randomize());
        out_result = instance_a.calculate(in_data);
    end
endmodule
module ClassInheritance (
    input logic [7:0] in_base_val,
    output logic [7:0] out_derived_val
);
    interface class MyInterface;
        pure virtual function void dummy_iface_method();
        pure virtual function int get_id();
    endclass
    class BaseClass;
        int base_member;
        function new(int val);
            base_member = val;
        endfunction
        virtual function int get_value();
            return base_member;
        endfunction
    endclass
    class DerivedClass extends BaseClass implements MyInterface;
        int derived_member;
        function new(int base_val, int derived_val);
            super.new(base_val);
            derived_member = derived_val;
        endfunction
        virtual function int get_value();
            return super.get_value() + derived_member;
        endfunction
        virtual function int get_id();
            return 42;
        endfunction
        virtual function void dummy_iface_method();
        endfunction
    endclass
    BaseClass base_inst;
    DerivedClass derived_inst;
    MyInterface iface_ref;
    always_comb begin
        out_derived_val = 8'h00;
        base_inst = new(in_base_val);
        derived_inst = new(in_base_val + 1, in_base_val + 2);
        out_derived_val = derived_inst.get_value();
        iface_ref = derived_inst;
        if (iface_ref != null) begin
            out_derived_val = out_derived_val + iface_ref.get_id();
            iface_ref.dummy_iface_method();
        end
    end
endmodule
module ClassStaticsAndParams (
    input logic in_trigger,
    output logic [15:0] out_status
);
    class ConfigClass;
        static int s_counter = 0;
        parameter int MAX_VAL = 100;
        int instance_val;
        function new(int val);
            instance_val = val;
            s_counter++;
        endfunction
        static function int get_static_count();
            return s_counter;
        endfunction
        function int get_scaled_value();
            return instance_val * MAX_VAL;
        endfunction
    endclass
    ConfigClass inst_cfg1, inst_cfg2;
    int current_static_count;
    int scaled_val1, scaled_val2;
    int sum_scaled_vals;
    always_comb begin
        out_status = 16'h0000;
        ConfigClass::s_counter = 0;
        inst_cfg1 = new(1);
        inst_cfg2 = new(2);
        current_static_count = ConfigClass::get_static_count();
        scaled_val1 = inst_cfg1.get_scaled_value();
        scaled_val2 = inst_cfg2.get_scaled_value();
        sum_scaled_vals = scaled_val1 + scaled_val2;
        out_status = {current_static_count[7:0], sum_scaled_vals[7:0]};
        if (in_trigger) begin
            out_status = out_status + 1;
        end
    end
endmodule
module ClassInitialBlocks (
    input logic in_reset,
    output logic [7:0] out_initial_val
);
    class InitialBlockTest;
        static int s_data_a = 15;
        int     m_data_b = 0;
        function new(int init_b);
            m_data_b = init_b;
        endfunction
        function int get_combined_data();
            return s_data_a + m_data_b;
        endfunction
    endclass
    InitialBlockTest inst_ib_a;
    InitialBlockTest inst_ib_b;
    initial begin
        InitialBlockTest::s_data_a = 50;
    end
    always_comb begin
        out_initial_val = 8'h00;
        inst_ib_a = new(1);
        inst_ib_b = new(2);
        out_initial_val = InitialBlockTest::s_data_a + inst_ib_a.m_data_b + inst_ib_b.m_data_b;
        if (in_reset) begin
            out_initial_val = 8'hFF;
        end
    end
endmodule
module ClassTypedefs (
    input logic [7:0] in_struct_val,
    output logic [15:0] out_typedef_result
);
    typedef packed struct {
        logic [7:0] sub_field;
    } AnonSubStruct_t;
    typedef packed struct {
        logic [3:0] field1;
        logic [3:0] field2;
        AnonSubStruct_t anon_sub_struct;
    } MyPackedStruct_t;
    typedef packed union {
        logic [15:0] combined;
        packed struct { 
            logic [7:0] byte0;
            logic [7:0] byte1;
        } bytes;
    } MyPackedUnion_t;
    class StructUnionClass;
        MyPackedStruct_t struct_member;
        MyPackedUnion_t union_member;
        function new();
        endfunction
        function int process_data(int input_data);
            struct_member.field1 = input_data[3:0];
            struct_member.field2 = input_data[7:4];
            struct_member.anon_sub_struct.sub_field = input_data[7:0];
            union_member.combined = {input_data[7:0], input_data[7:0]};
            return struct_member.field1 + struct_member.anon_sub_struct.sub_field + union_member.bytes.byte0;
        endfunction
    endclass
    StructUnionClass struct_union_inst;
    int processed_val;
    always_comb begin
        out_typedef_result = 16'h0000;
        struct_union_inst = new();
        processed_val = struct_union_inst.process_data(in_struct_val);
        out_typedef_result = processed_val;
        out_typedef_result = out_typedef_result + struct_union_inst.struct_member.anon_sub_struct.sub_field;
    end
endmodule
module ClassAndPkgInteraction (
    input logic clk_in,
    input logic [7:0] in_data,
    output logic [15:0] out_status
);
    import my_global_pkg::*;
    PkgGlobalClass pkg_inst;
    PkgPackedStruct_t pkg_struct_var;
    PkgCoverGroup pkg_cg_inst;
    always_comb begin
        out_status = 16'h0000;
        pkg_inst = new(in_data);
        pkg_struct_var.field_a = in_data[3:0];
        pkg_struct_var.field_b = in_data[7:4];
        pkg_inst.static_pkg_task(); 
        out_status = pkg_inst.get_pkg_data();
        out_status = out_status + PkgGlobalClass::get_pkg_counter();
        pkg_cg_inst = new(in_data, clk_in);
        pkg_cg_inst.sample();
        out_status = out_status + pkg_struct_var.field_a;
    end
endmodule
module ClassCoverageAndDPI (
    input logic clk,
    input logic [3:0] in_cov_val,
    output logic [7:0] out_sum
);
    import my_global_pkg::*; 
    class CoverageDPIClass;
        logic [7:0] internal_data;
        PkgCoverGroup my_pkg_cg_inst; 
        function new(logic clk_signal, logic [3:0] in_cov_val_ref);
            my_pkg_cg_inst = new(internal_data, clk_signal); 
            internal_data = 0; 
        endfunction
        function void set_data(logic [7:0] val);
            internal_data = my_global_pkg::c_add_one(val); 
            my_pkg_cg_inst.sample();
        endfunction
    endclass
    CoverageDPIClass cov_dpi_inst;
    always_comb begin
        out_sum = 8'h00;
        cov_dpi_inst = new(clk, in_cov_val);
        cov_dpi_inst.set_data(in_cov_val);
        out_sum = cov_dpi_inst.internal_data;
    end
endmodule
