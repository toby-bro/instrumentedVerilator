timeunit 1ns;
timeprecision 1ps;
module Module_BasicOps (
    input logic [7:0] in_data_a,
    input logic [7:0] in_data_b,
    input bit         in_bit,
    input real        in_real_val,
    output logic [7:0] out_result,
    output logic      out_single_bit,
    output real       out_real_result
);
    logic [7:0] temp_wire_1;
    logic [7:0] temp_wire_2;
    logic [7:0] temp_wire_3;
    logic       temp_bool;
    real        temp_real_1;
    real        temp_real_2;
    string      string_a = "hello";
    string      string_b = "world";
    assign out_result[0]    = ~in_data_a[0];
    assign out_single_bit   = !in_bit;
    assign temp_wire_1[0]   = &in_data_a;
    assign temp_wire_2[0]   = |in_data_b;
    assign temp_wire_3[0]   = ^in_data_a[0];
    assign out_real_result  = +in_real_val;
    assign temp_real_1      = -in_real_val;
    assign temp_wire_1      = in_data_a + in_data_b;
    assign temp_wire_2      = in_data_a - in_data_b;
    assign temp_wire_3      = in_data_a * in_data_b;
    assign temp_wire_1      = in_data_a / in_data_b;
    assign temp_wire_2      = in_data_a % in_data_b;
    assign temp_bool        = in_data_a == in_data_b;
    assign temp_bool        = in_data_a != in_data_b;
    assign temp_bool        = in_data_a === 8'bx;
    assign temp_bool        = in_data_a !== 8'bx;
    assign temp_bool        = in_data_a > in_data_b;
    assign temp_bool        = in_data_a < in_data_b;
    assign temp_bool        = in_data_a >= in_data_b;
    assign temp_bool        = in_data_a <= in_data_b;
    assign temp_bool        = in_data_a && in_data_b;
    assign temp_bool        = in_data_a || in_data_b;
    assign temp_wire_1      = in_data_a & in_data_b;
    assign temp_wire_2      = in_data_a | in_data_b;
    assign temp_wire_3      = in_data_a ^ in_data_b;
    assign temp_wire_1      = in_data_a ~^ in_data_b;
    assign temp_wire_2      = in_data_a << 1;
    assign temp_wire_3      = in_data_a >> 1;
    assign temp_wire_1      = in_data_a <<< 1;
    assign temp_wire_2      = in_data_a >>> 1;
    assign temp_bool        = string_a == string_b;
    assign temp_bool        = string_a === string_b;
    assign temp_bool        = in_real_val == temp_real_1;
    assign temp_bool        = in_data_a inside { [0:10], 20, [30:40] };
    assign out_result       = in_bit ? in_data_a : in_data_b;
    assign temp_real_2      = real'(in_data_a);
    assign out_real_result  = $bits(in_data_a);
    wire [7:0] my_wire;
    assign my_wire = in_data_a + 1;
    assign out_result = my_wire;
    parameter int PARAM_INT = 100;
    parameter real PARAM_REAL = 3.14;
    parameter string PARAM_STRING = "Hello";
    localparam [3:0] FIXED_RANGE_LP = 4'hA;
    localparam UNSIZED_LP = 123;
    logic [31:0] large_logic_var;
    logic [15:0] medium_logic_var;
    logic        small_logic_var;
    logic [63:0] quad_logic_var;
    assign large_logic_var[0] = in_bit;
    assign medium_logic_var[0] = in_bit;
    assign small_logic_var = in_bit;
    assign quad_logic_var[0] = in_bit;
    localparam int CONST_VAL_1 = 123;
    localparam int CONST_VAL_2 = 123;
    localparam int CONST_VAL_3 = 456;
    assign out_result = (in_data_a + CONST_VAL_1);
    wire (pull1, pull0) my_strong_wire;
    assign my_strong_wire = 1'b1;
    assign out_result = out_result & my_strong_wire;
endmodule
module Module_ComplexTypesAndSelects (
    input logic [7:0] in_val,
    input logic [1:0] in_idx_2bit,
    input logic [3:0] in_idx_4bit,
    output logic [7:0] out_sel_data,
    output logic [15:0] out_struct_field
);
    timeunit 1ns;
    timeprecision 1ps;
    typedef enum logic [1:0] {
        STATE_IDLE = 2'b00,
        STATE_RUN  = 2'b01,
        STATE_STOP = 2'b10,
        STATE_ERROR = 2'b11
    } FSM_STATE_T;
    FSM_STATE_T current_state;
    assign current_state = FSM_STATE_T'(in_idx_2bit);
    typedef struct packed {
        logic [7:0] field_a;
        logic [7:0] field_b;
    } MyPackedStruct_t;
    MyPackedStruct_t ps_var;
    assign ps_var.field_a = in_val;
    assign ps_var.field_b = in_val + 1;
    assign out_struct_field = ps_var.field_a;
    typedef struct {
        logic [7:0] unpacked_field_c;
        logic [7:0] unpacked_field_d;
    } MyUnpackedStruct_t;
    MyUnpackedStruct_t ups_var;
    assign ups_var.unpacked_field_c = in_val;
    assign ups_var.unpacked_field_d = in_val - 1;
    logic [7:0] packed_array [3:0];
    assign packed_array[in_idx_2bit] = in_val;
    assign out_sel_data = packed_array[in_idx_2bit];
    logic [7:0] unpacked_array [0:1][0:2];
    assign unpacked_array[0][in_idx_2bit] = in_val;
    assign out_sel_data = unpacked_array[0][in_idx_2bit];
    logic [15:0] nested_array [1:0][7:0];
    assign nested_array[in_idx_2bit][in_val] = {in_val, in_val};
    assign out_struct_field = nested_array[in_idx_2bit][in_val];
    assign out_sel_data = in_val[3:0];
    assign out_sel_data = in_val[in_idx_2bit +: 4];
    assign out_sel_data = in_val[7 -: 4];
    logic dyn_array_sig [];
    always_comb begin : dyn_array_block
        dyn_array_sig = new [4];
        dyn_array_sig[0] = in_val[0];
        void'(dyn_array_sig.size());
        dyn_array_sig.delete();
        dyn_array_sig = new [0];
    end
    logic queue_sig [$];
    always_comb begin : queue_block
        queue_sig = '{default: in_val[0], 0: in_val[1]};
        queue_sig.push_back(in_val[2]);
        void'(queue_sig.pop_front());
        void'(queue_sig.size());
        logic [7:0] empty_queue_var [$];
        empty_queue_var = {};
    end
    logic [7:0] assoc_array_sig [int];
    always_comb begin : assoc_array_block
        assoc_array_sig[0] = in_val;
        void'(assoc_array_sig.delete(0));
        if (assoc_array_sig.exists(0)) begin end
        void'(assoc_array_sig.first(0));
        void'(assoc_array_sig.last(0));
        void'(assoc_array_sig.next(0));
        void'(assoc_array_sig.prev(0));
    end
    localparam struct packed { int x; int y; } POINT_CONST_A = '{x:10, y:20};
    localparam struct packed { int x; int y; } POINT_CONST_B = '{x:10, y:20};
    localparam logic [7:0] CONST_ARRAY_A [3:0] = '{8'hAA, 8'hBB, 8'hCC, 8'hDD};
    localparam logic [7:0] CONST_ARRAY_B [3:0] = '{8'hAA, 8'hBB, 8'hCC, 8'hDD};
    typedef logic [15:0] WORD_T;
    WORD_T my_word_var;
    assign my_word_var = in_val;
    typedef struct {
        WORD_T field1;
        FSM_STATE_T field2;
    } COMPLEX_STRUCT_T;
    COMPLEX_STRUCT_T complex_var;
    assign complex_var.field1 = in_val;
    assign complex_var.field2 = current_state;
    assign out_struct_field = complex_var.field1;
    function void my_void_function();
    endfunction
    assign out_sel_data[0] = in_val[0];
endmodule
module Module_ControlFlow (
    input logic       clk,
    input logic       reset,
    input logic [3:0] data_in,
    input logic [1:0] sel,
    output logic [3:0] data_out_ff,
    output logic [3:0] data_out_comb,
    output logic [3:0] data_out_latch,
    output logic [3:0] data_out_for,
    output logic [3:0] data_out_while
);
    timeunit 1ns;
    timeprecision 1ps;
    logic [3:0] reg_ff;
    logic [3:0] reg_latch;
    logic [3:0] reg_for;
    logic [3:0] reg_while;
    always_ff @(posedge clk or posedge reset) begin : FF_BLOCK
        if (reset) begin
            reg_ff <= 4'b0;
        end else begin
            reg_ff <= data_in;
        end
    end
    assign data_out_ff = reg_ff;
    always_comb begin : COMB_BLOCK
        data_out_comb = data_in + 1;
    end
    always_latch begin : LATCH_BLOCK
        if (sel == 2'b00) reg_latch = data_in;
        else if (sel == 2'b01) reg_latch = data_in + 1;
        else reg_latch = 4'b0;
    end
    assign data_out_latch = reg_latch;
    always_comb begin
        if (data_in > 4'd5) begin
            data_out_for = data_in;
        end else begin
            data_out_for = 4'b0;
        end
    end
    always_comb begin
        unique case (sel)
            2'b00: data_out_while = 4'd1;
            2'b01: data_out_while = 4'd2;
            2'b10: data_out_while = 4'd3;
            default: data_out_while = 4'd4;
        endcase
    end
    genvar i;
    generate
        for (i = 0; i < 4; i++) begin : loop_for_data
            assign data_out_for[i] = data_in[i];
        end
    endgenerate
    integer j;
    always_comb begin : while_loop_block
        j = 0;
        while (j < 4) begin
            reg_while[j] = data_in[j];
            j++;
        end
    end
    assign data_out_while = reg_while;
    always_ff @(posedge clk) begin
        fork : my_fork_block
            begin
                if (data_in == 4'd1) reg_ff <= 4'd11;
            end
            begin
                if (data_in == 4'd2) reg_ff <= 4'd22;
            end
        join_none
    end
    always_comb begin : outer_loop_block_jump
        integer k = 0;
        while (k < 5) begin : inner_loop_block_jump
            k++;
            if (k == 2) disable inner_loop_block_jump;
            if (k == 4) disable outer_loop_block_jump;
            data_out_comb[k-1] = data_in[k-1];
        end
    end
    logic [63:0] current_time;
    assign current_time = $time;
    logic [63:0] current_realtime;
    assign current_realtime = $realtime;
    logic [7:0] streamed_data;
    assign {>>{streamed_data}} = data_in;
    always_ff @(posedge clk) begin : await_block
        await (data_in == 4'd3);
        reg_ff <= 4'd5;
    end
endmodule
interface my_interface (input logic clk_i);
    logic [7:0] data;
    logic enable;
    modport master (output data, output enable, input clk_i);
    modport slave (input data, input enable, input clk_i);
    function void get_data(output logic [7:0] d);
        d = data;
    endfunction
    function void set_data(input logic [7:0] d);
        data = d;
    endfunction
    modport full_access (output data, input enable, input clk_i, function get_data, function set_data);
endinterface
module Module_ClassesAndDPI (
    input logic in_bit_dpi,
    output logic out_bit_dpi
);
    timeunit 1ns;
    timeprecision 1ps;
    import "DPI-C" function int dpi_add(int a, int b);
    import "DPI-C" pure function int dpi_multiply(int a, int b);
    import "DPI-C" context function void dpi_context_func();
    export "DPI-C" function my_sv_task;
    function automatic void my_sv_task(input int val);
        out_bit_dpi = (val > 0);
    endfunction
    class MyBaseClass;
        rand int value_base;
        constraint c_value_base { value_base >= 0; }
        function new(int v);
            this.value_base = v;
        endfunction
        virtual function void print_value();
        endfunction
        function void extern_method();
        endfunction
    endclass
    class MyExtendedClass extends MyBaseClass;
        rand int value_ext;
        constraint c_value_ext { soft value_ext < 100; }
        constraint c_total { value_base + value_ext < 150; }
        function new(int vb, int ve);
            super.new(vb);
            this.value_ext = ve;
        endfunction
        function void print_value();
        endfunction
    endclass
    MyBaseClass base_obj_handle;
    MyExtendedClass ext_obj_handle;
    logic [31:0] dpi_result_wire;
    logic dpi_context_trigger_var;
    always_comb begin
        if (base_obj_handle == null) begin
            base_obj_handle = new(1);
        end
        if (ext_obj_handle == null) begin
            ext_obj_handle = new(10, 20);
        end
        void'(base_obj_handle.randomize() with { base_obj_handle.value_base > 5; });
        dpi_result_wire = dpi_add(10, 20);
        dpi_result_wire = dpi_multiply(dpi_result_wire, 2);
        if (dpi_context_trigger_var) begin
            dpi_context_func();
        end
    end
    assign out_bit_dpi = in_bit_dpi;
endmodule
module Module_InterfacesAndHierarchy (
    input logic clk,
    input logic rst,
    input  logic [7:0] in_val_mod,
    output logic [7:0] out_val_mod
);
    timeunit 1ns;
    timeprecision 1ps;
    my_interface if_inst (.clk_i(clk));
    SubModule_Example sub_inst (.in_sub(in_val_mod), .out_sub(out_val_mod));
    logic [7:0] cross_hier_data;
    assign cross_hier_data = sub_inst.internal_reg;
    always_comb begin : named_block_in_iface_mod
        logic [7:0] block_local_var;
        block_local_var = in_val_mod + 2;
        out_val_mod = block_local_var;
    end
    clocking cb @(posedge clk);
        default input #1step output #1ns;
        input in_val_mod;
        output out_val_mod;
    endclocking
endmodule
module SubModule_Example (
    input logic [7:0] in_sub,
    output logic [7:0] out_sub
);
    timeunit 1ns;
    timeprecision 1ps;
    logic [7:0] internal_reg;
    assign out_sub = in_sub;
    assign internal_reg = in_sub + 1;
endmodule
module Module_AssertionsAndCoverage (
    input logic clk,
    input logic enable,
    input logic condition,
    input logic [1:0] state_vec,
    output logic out_assert_status
);
    timeunit 1ns;
    timeprecision 1ps;
    logic asserted_condition;
    assign asserted_condition = (state_vec == 2'b11);
    always_comb begin
        assert (condition) begin end
    end
    property p_enable_data;
        @(posedge clk) (enable) |=> (state_vec != 2'b00);
    endproperty
    A1: assert property (p_enable_data);
    property p_state_transition;
        @(posedge clk) (state_vec == 2'b00) |-> (state_vec == 2'b01);
    endproperty
    C1: cover property (p_state_transition);
    covergroup my_state_cg @(posedge clk);
        cp_state : coverpoint state_vec {
            bins zero = {2'b00};
            bins one = {2'b01};
            bins two = {2'b10};
            bins three = {2'b11};
        }
        cross cp_state, enable;
    endgroup
    my_state_cg cg_inst;
    assign out_assert_status = asserted_condition;
endmodule
module Module_AdvancedTypes (
    input logic [63:0] in_long_data,
    input logic [7:0] key_val,
    output logic [7:0] out_ret_val
);
    timeunit 1ns;
    timeprecision 1ps;
    typedef logic signed [63:0] SIGNED_QWORD;
    SIGNED_QWORD signed_var;
    assign signed_var = in_long_data;
    typedef struct packed {
        logic [7:0] byte_field;
        logic [7:0] next_byte;
    } LITERAL_STRUCT_T;
    LITERAL_STRUCT_T literal_struct_var;
    assign literal_struct_var.byte_field = in_long_data[7:0];
    logic [7:0] temp_literal_field;
    assign temp_literal_field = literal_struct_var.byte_field;
    const logic [7:0] CONST_BYTE = 8'hFF;
    logic [7:0] temp_const_byte;
    assign temp_const_byte = CONST_BYTE;
    static logic [7:0] static_byte;
    always_comb static_byte = in_long_data[7:0];
    logic [7:0] temp_static_byte;
    assign temp_static_byte = static_byte;
    class MyRandomizer;
        rand logic [7:0] rand_val;
        constraint c_rand_val { rand_val > 50; }
    endclass
    MyRandomizer rand_obj_handle;
    always_comb begin : rand_block
        if (rand_obj_handle == null) begin
            rand_obj_handle = new();
        end
        void'(rand_obj_handle.randomize());
    end
    logic [7:0] temp_rand_val;
    assign temp_rand_val = rand_obj_handle.rand_val;
    wire pd_net;
    wire pu_net;
    pulldown pd_inst (pd_net);
    pullup pu_inst (pu_net);
    logic dummy_pd;
    logic dummy_pu;
    assign dummy_pd = pd_net;
    assign dummy_pu = pu_net;
    localparam string STR_CONST = "Verilator coverage test";
    localparam int ARR_CONST [2] = '{1, 2};
    assign out_ret_val = temp_literal_field + temp_const_byte + temp_static_byte + temp_rand_val;
endmodule
