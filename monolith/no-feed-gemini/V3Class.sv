module BasicClassProcessor (
    input logic [7:0] in_data,
    output logic [7:0] out_data
);
    class MyBasicClass;
        static int s_counter = 0; 
        parameter int MAX_VAL = 100; 
        localparam int LP_VAL = 200; 
        int instance_id;
        static function int get_static_count(); 
            s_counter++;
            return s_counter;
        endfunction
        function new(int id);
            this.instance_id = id;
        endfunction
        function void process_val(input int val);
            s_counter += val;
        endfunction
        initial begin 
            s_counter = 5; 
        end
        initial static begin 
        end
    endclass
    MyBasicClass cls_inst;
    MyBasicClass cls_inst2;
    always_comb begin
        if (in_data == 8'h00) begin
            cls_inst = new(1);
            cls_inst2 = new(2);
        end else begin
            if (cls_inst != null) begin
                cls_inst.process_val(in_data);
            end
            if (cls_inst2 != null) begin
                cls_inst2.process_val(in_data + 1);
            end
        end
        out_data = MyBasicClass::get_static_count() + in_data;
    end
endmodule
module ClassHierarchyProcessor (
    input logic [3:0] in_op,
    output logic [7:0] out_result
);
    interface class IVirtualInterface; 
        pure virtual function int calculate(int a, int b);
        pure virtual function void log_event();
    endclass
    class BaseClass extends IVirtualInterface; 
        protected int base_val;
        function new(int val);
            this.base_val = val;
        endfunction
        virtual function int calculate(int a, int b);
            return a + b + base_val;
        endfunction
        virtual function void log_event();
        endfunction
    endclass
    class DerivedClass extends BaseClass implements IVirtualInterface; 
        int derived_val;
        function new(int b_val, int d_val);
            super.new(b_val);
            this.derived_val = d_val;
        endfunction
        virtual function int calculate(int a, int b);
            return super.calculate(a, b) * derived_val;
        endfunction
        virtual function void log_event();
        endfunction
    endclass
    DerivedClass inst_derived;
    always_comb begin
        if (in_op == 4'h0) begin
            inst_derived = new(5, 2);
        end else if (in_op == 4'h1) begin
            if (inst_derived != null) begin
                out_result = inst_derived.calculate(in_op, 3);
                inst_derived.log_event();
            end else begin
                out_result = 0;
            end
        end else begin
            out_result = 0;
            if (inst_derived != null) begin
                inst_derived.log_event();
            end
        end
    end
endmodule
module TypeDeclarationProcessor (
    input logic [1:0] in_sel,
    output logic [15:0] out_val
);
    class MyTypesContainer;
        typedef struct packed { 
            logic [7:0] byte_h;
            logic [7:0] byte_l;
        } my_byte_pair_t;
        public typedef struct packed { 
            int field1;
            my_byte_pair_t pair_data;
            struct packed { 
                logic [3:0] nibble1;
                logic [3:0] nibble2;
            } anon_data;
        } my_public_struct_t;
        typedef union packed { 
            int as_int;
            logic [15:0] as_bits;
            my_byte_pair_t as_pair;
        } my_union_t;
        my_public_struct_t pub_inst;
        my_union_t union_inst;
        function new();
            pub_inst.field1 = 123;
            pub_inst.pair_data.byte_h = 8'hAA;
            pub_inst.pair_data.byte_l = 8'hBB;
            pub_inst.anon_data.nibble1 = 4'h1;
            pub_inst.anon_data.nibble2 = 4'h2;
            union_inst.as_int = 16'hFFFF;
        endfunction
        function automatic logic [15:0] get_value(input logic [1:0] sel);
            if (sel == 2'b00) return pub_inst.pair_data.byte_h;
            else if (sel == 2'b01) return pub_inst.pair_data.byte_l;
            else if (sel == 2'b10) return union_inst.as_bits;
            else return {pub_inst.anon_data.nibble1, pub_inst.anon_data.nibble2};
        endfunction
    endclass
    MyTypesContainer type_inst;
    always_comb begin
        if (type_inst == null) begin
            type_inst = new();
        end
        out_val = type_inst.get_value(in_sel);
    end
endmodule
module AdvancedClassFeatures (
    input logic [2:0] in_dpi_val,
    output logic out_hit
);
    import "DPI-C" function int dpi_get_magic_number(); 
    class MyAdvancedClass;
        int m_data;
        covergroup my_covergroup @(posedge m_data);
            coverpoint m_data {
                bins low = {0, 1};
                bins high = {2, 3};
                illegal_bins illegal = {7};
            }
            cross m_data, m_data; 
        endgroup
        function new(int init_data);
            this.m_data = init_data;
            my_covergroup = new(); 
        endfunction
        function void set_data(input int val);
            this.m_data = val;
            my_covergroup.sample(); 
        endfunction
        function bit check_magic(input int val);
            return (val == dpi_get_magic_number());
        endfunction
    endclass
    MyAdvancedClass adv_inst;
    always_comb begin
        if (adv_inst == null) begin
            adv_inst = new(0);
        end
        adv_inst.set_data(in_dpi_val);
        out_hit = adv_inst.check_magic(in_dpi_val);
    end
endmodule
