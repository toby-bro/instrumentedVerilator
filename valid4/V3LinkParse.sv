primitive my_unnamed_udp_primitive(
    output Q,
    input A,
    input B
);
    table
      0 0 : 0;
      0 1 : 1;
      1 0 : 1;
      1 1 : 0;
    endtable
endprimitive
package my_package;
    typedef enum {
        PKG_STATE_IDLE,
        PKG_STATE_RUNNING
    } PkgState_t;
    function automatic int get_factor();
        return 2;
    endfunction
endpackage
module DataTypeModule (
    input logic [7:0] in_data,
    output logic [7:0] out_data
);
    enum {
        STATE_IDLE_IMPLICIT,
        STATE_RUNNING_IMPLICIT,
        STATE_PAUSED_IMPLICIT
    } current_state_implicit;
    typedef enum {
        RED = 1,
        GREEN = 2,
        BLUE = 4
    } Color_t;
    Color_t my_color = RED;
    typedef enum {
        ITEM_ZERO,
        ITEM_ONE,
        ITEM_RANGE_VALS [/* verilator enum_expand */0:2],
        ITEM_THREE
    } Items_t;
    Items_t enum_item_test = ITEM_ZERO;
    struct {
        int x;
        int y;
    } coords_implicit, more_coords_implicit;
    typedef struct packed {
        logic [3:0] field_a;
        logic [3:0] field_b;
    } MyStruct_t;
    MyStruct_t s_inst;
    logic [7:0] internal_reg;
    parameter int PARAM_VAL = 10;
    localparam int LOCAL_PARAM_VAL = PARAM_VAL + 5;
    always_comb begin : update_data_block
        internal_reg = in_data + 1;
        out_data = internal_reg;
        current_state_implicit = STATE_RUNNING_IMPLICIT;
        my_color = GREEN;
        s_inst.field_a = 4'hA;
        s_inst.field_b = '1;
        coords_implicit.x = 100;
        more_coords_implicit.y = 200;
    end
    function int my_func_for_implicit_static(input int val_in);
        int local_var_with_init = 10;
        local_var_with_init = val_in * 2;
        return local_var_with_init;
    endfunction
    always_comb begin : loop_static_test_block
    end
    assign out_data = out_data + my_func_for_implicit_static(in_data);
endmodule
module ProceduralModule (
    input logic [3:0] in_val,
    output logic [3:0] out_val
);
    logic [3:0] internal_proc_reg;
    logic [3:0] func_result_reg;
    logic [3:0] delayed_out_sig;
    logic my_clk;
    initial begin : initial_block
        internal_proc_reg = 4'hF;
    end
    final begin : final_block
    end
    always_ff @(posedge in_val[0]) begin : ff_block
        internal_proc_reg <= in_val;
        func_result_reg <= my_auto_function(in_val);
    end
    always_comb begin : comb_block
        out_val = internal_proc_reg + 1;
    end
    always_latch begin : latch_block
        if (in_val[1]) begin
            internal_proc_reg = in_val;
        end
    end
    always begin : event_control_internal_test
        @(posedge my_clk);
        out_val = in_val;
    end
    function automatic logic [3:0] my_auto_function(input logic [3:0] a);
        logic [3:0] local_auto_var = 0;
        local_auto_var = a * 2;
        return local_auto_var;
    endfunction
    task static my_static_task(input logic [3:0] b, output logic [3:0] c);
        static logic [3:0] local_static_var = 0;
        local_static_var = b + 1;
        c = local_static_var;
    endtask
    always_comb begin : task_call_block
        logic [3:0] task_output;
        my_static_task(in_val[3:0], task_output);
        if (task_output > 0) out_val = task_output;
    end
    assign delayed_out_sig = in_val;
    assign out_val = out_val + delayed_out_sig;
endmodule
module ControlFlowModule (
    input logic [2:0] selector,
    input logic [7:0] data_in,
    output logic [7:0] data_out
);
    logic [7:0] internal_data;
    logic [3:0] foreach_array [4];
    int sum_foreach = 0;
    initial begin
        foreach (foreach_array[i]) begin
            foreach_array[i] = i;
        end
    end
    always_comb begin : main_control_block
        if (selector[0])
            internal_data = data_in;
          internal_data = 8'h00;
        if (selector[1]) begin : then_block
            internal_data = data_in + 1;
        end else begin : else_block
            internal_data = 8'hFF;
        end
        case (selector[2])
            1'b0: data_out = internal_data + 1;
            1'b1: data_out = internal_data - 1;
            default: data_out = internal_data;
        endcase
        repeat (3) begin : repeat_loop
            static int repeat_static_var = 1;
            internal_data = internal_data + repeat_static_var;
        end
        do begin : do_while_loop
            internal_data = internal_data - 1;
        end while (internal_data > 0);
        wait(0);
        wait(selector[0] == 1'b1);
        while (selector[1] && internal_data < 8'hF0)
            internal_data = internal_data + 2;
          if (data_in[0]) internal_data = internal_data;
        begin : my_named_block
            logic [7:0] temp_val = data_in;
            data_out = temp_val;
        end
        begin
            logic [7:0] another_temp_val = data_in * 2;
            data_out = another_temp_val;
        end
        sum_foreach = 0;
        foreach (foreach_array[idx]) begin : foreach_loop
            sum_foreach = sum_foreach + foreach_array[idx];
        end
        data_out = data_out + sum_foreach;
    end
endmodule
module GenHierarchyModule (
    input logic [1:0] gen_sel,
    output logic [7:0] out_val
);
    my_unnamed_udp_primitive (
        .Q(out_val[0]),
        .A(gen_sel[0]),
        .B(gen_sel[1])
    );
    generate if (gen_sel[0]) begin : gen_if_outer_true
        assign out_val[7] = 1'b0;
    end else
        if (gen_sel[1]) begin : gen_if_inner_true
            logic [7:0] gen_data_a = 8'hAA;
            assign out_val = gen_data_a;
        end else begin : gen_if_inner_false
            logic [7:0] gen_data_b = 8'hBB;
            assign out_val = gen_data_b;
        end
    endgenerate
    generate case (gen_sel)
        2'b00: begin : gen_case_00
            assign out_val = 8'h00;
        end
        2'b01: begin
            assign out_val = 8'h01;
        end
        default: begin : gen_case_default
            assign out_val = 8'hFF;
        end
    endcase
    endgenerate
endmodule
module ClassConstraintModule (
    input logic enable_constraint,
    output logic [7:0] constrained_val
);
    import my_package::get_factor;
    class BaseClass;
        int base_val;
        function new();
            base_val = 1;
        endfunction
    endclass
    class DerivedClass extends BaseClass;
        int derived_val;
        function new();
            super.new();
            derived_val = 0;
            derived_val = base_val + 1;
        endfunction
    endclass
    class MyClass;
        rand int value_c;
        rand int factor_c;
        constraint c_rand_val {
            value_c inside {[0:100]};
            factor_c == get_factor();
        }
        function new();
            value_c = 0;
            factor_c = 0;
        endfunction
        function automatic logic [7:0] calculate();
            return value_c + factor_c;
        endfunction
    endclass
    MyClass my_instance;
    DerivedClass derived_instance;
    always_comb begin : class_proc_block
        if (my_instance == null) begin
            my_instance = new();
        end
        if (derived_instance == null) begin
            derived_instance = new();
        end
        if (my_instance != null) begin
            if (enable_constraint) begin
                my_instance.value_c = 50;
                my_instance.factor_c = get_factor();
            end else begin
                my_instance.value_c = 10;
                my_instance.factor_c = 1;
            end
            constrained_val = my_instance.calculate();
        end else begin
            constrained_val = 8'hX;
        end
    end
endmodule
`timescale 1ns/100ps
module TimeSystemTaskModule (
    input logic clk,
    output logic [63:0] current_time_out
);
    timeunit 1ps;
    timeprecision 1fs;
    always_ff @(posedge clk) begin : time_task_block
        current_time_out <= $time;
        current_time_out <= $realtime;
        current_time_out <= $sformatf("Current time: %0t", $time);
        current_time_out <= $timeunit;
        current_time_out <= $timeprecision;
        current_time_out <= $printtimescale;
    end
    assign current_time_out = current_time_out + 1;
endmodule
module AttributeClockingModule (
    input logic clk_in,
    input logic rst_n,
    input logic [7:0] data_in,
    output logic [7:0] data_out
);
typedef /* verilator public */ enum { A, B } MyEnum_pubdt_t;
MyEnum_pubdt_t enum_pubdt_var;
logic /* verilator clock_enable */ clock_enable_sig_attr;
logic /* verilator forceable */ forceable_sig;
logic /* verilator public */ public_sig;
logic /* verilator public_flat */ public_flat_sig;
logic /* verilator public_flat_rd */ public_flat_rd_sig;
logic /* verilator public_flat_rw */ public_flat_rw_sig;
logic /* verilator isolate_assignments */ isolate_assign_sig;
logic /* verilator sformat */ sformat_sig_attr;
logic /* verilator split_var */ split_var_sig;
logic [31:0] /* verilator sc_bv */ sc_bv_sig;
logic /* verilator clocker */ is_clocker_sig;
logic /* verilator no_clocker */ no_clocker_sig;
logic [7:0] my_input_cb;
logic [7:0] my_output_cb;
logic [7:0] output_from_assign;
clocking cb @(posedge clk_in);
    input data_in;
    output data_out;
    input #2ns my_input_cb;
    output #1step my_output_cb;
    default input #3ns;
    default output #1ns;
endclocking
assign data_out = cb.data_out + 1 + cb.my_input_cb[0];
assign output_from_assign = forceable_sig;
always_ff @(posedge clk_in, negedge rst_n) begin
    if (!rst_n) begin
        forceable_sig <= 0;
        public_sig <= 0;
        public_flat_sig <= 0;
        public_flat_rd_sig <= 0;
        public_flat_rw_sig <= 0;
        isolate_assign_sig <= 0;
        sformat_sig_attr <= 0;
        split_var_sig <= 0;
        sc_bv_sig <= 0;
        is_clocker_sig <= 0;
        no_clocker_sig <= 0;
        enum_pubdt_var <= A;
        clock_enable_sig_attr <= 0;
        my_input_cb <= 0;
        my_output_cb <= 0;
        output_from_assign <= 0;
    end else begin
        forceable_sig <= data_in[0];
        public_sig <= data_in[1];
        public_flat_sig <= data_in[2];
        public_flat_rd_sig <= data_in[3];
        public_flat_rw_sig <= data_in[4];
        isolate_assign_sig <= data_in[5];
        sformat_sig_attr <= data_in[6];
        split_var_sig <= data_in[7];
        sc_bv_sig <= {31'b0, data_in[0]};
        is_clocker_sig <= data_in[1];
        no_clocker_sig <= data_in[2];
        enum_pubdt_var <= B;
        clock_enable_sig_attr <= data_in[3];
        my_input_cb <= data_in + 1;
        my_output_cb <= data_in + 2;
        output_from_assign <= data_in + 3;
    end
end
endmodule
module RandomCoverageModule (
    input logic clk,
    input logic reset,
    input logic enable_rand,
    output logic [7:0] rand_output
);
    class MyRandomClass;
        rand int r_val;
        rand int weight;
        constraint c_rand_val {
            r_val inside {[10:20], [50:60]};
            weight > 0;
            weight <= 10;
        }
        function new();
            r_val = 0;
            weight = 0;
        endfunction
    endclass
    MyRandomClass rand_inst;
    int coverage_var;
    restrict (enable_rand);
    covergroup my_covergroup @(posedge clk);
        option.per_instance = 1;
        cp_rand_output : coverpoint rand_output {
            bins low = {10, 11, 12};
            bins high = {50, 51, 52};
            bins other = default;
        }
        cp_coverage_var : coverpoint coverage_var;
    endgroup
    my_covergroup cover_inst;
    initial begin
        cover_inst = new();
    end
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            rand_inst = null;
            coverage_var = 0;
            rand_output <= 8'h00;
        end else begin
            if (rand_inst == null) begin
                rand_inst = new();
            end
            rand_inst.r_val = enable_rand ? 15 : 55;
            rand_inst.weight = enable_rand ? 5 : 1;
            rand_output <= rand_inst.r_val;
            coverage_var <= rand_output;
        end
    end
endmodule
