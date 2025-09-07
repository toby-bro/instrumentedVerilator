package my_package;
    function int pkg_func(int val);
        return val + 10;
    endfunction
endpackage
module LifeTimeAndProcedures #(parameter P_VAL = 1) (
    input logic in_data,
    output logic out_result
);
    timeunit 1ns;
    timeprecision 1ps;
    parameter int PARAM_NO_DEFAULT; 
    parameter int PARAM_WITH_DEFAULT = P_VAL + 10; 
    localparam int LOCAL_PARAM = 20;
    var int my_static_mod_var = 1; 
    var automatic int my_auto_mod_var = 2; 
    logic [3:0] unbased_unsized_literal = '0; 
    function automatic int my_auto_func (input int a, input int b);
        int local_func_auto_var = a + b; 
        return local_func_auto_var;
    endfunction
    function static int my_static_func (input int val);
        int static_local_func_var = val + 1; 
        return static_local_func_var;
    endfunction
    task my_task (input logic [7:0] data_in_task, output logic [7:0] data_out_task);
        automatic logic [7:0] temp_data;
        temp_data = data_in_task;
        data_out_task = temp_data;
    endtask
    always_ff @(posedge in_data) begin : ff_block
        out_result <= in_data;
        if (in_data)
        out_result <= in_data; 
        else
            out_result <= ~in_data;
    end
    always_comb @(in_data) begin : comb_block_error 
        my_static_mod_var = my_auto_func(PARAM_WITH_DEFAULT, LOCAL_PARAM);
        my_static_mod_var = my_static_func(my_static_mod_var);
    end
    logic [7:0] task_input_val = 8'd5;
    logic [7:0] task_output_val;
    always_comb begin
        task_output_val = 8'h0; 
        my_task(task_input_val, task_output_val);
        out_result = task_output_val[0];
    end
endmodule
module TypedefsAndImplicitTypes (
    input logic [3:0] in_value,
    output logic [7:0] out_status
);
    typedef enum logic [1:0] {
        STATE_IDLE,
        STATE_RUNNING = 2'd1,
        STATE_PAUSED,
        STATE_STOPPED = 2'd3
    } my_enum_t;
    my_enum_t current_state = STATE_IDLE;
    typedef struct packed {
        logic [7:0] addr;
        logic [7:0] data;
    } my_struct_t;
    my_struct_t packet_info;
    typedef enum int {
        ZERO_EXPAND = 0,
        ONE_TO_FIVE [1:5] = 1, 
        TEN_EXPAND = 10
    } expanded_enum_t;
    expanded_enum_t my_expanded_val;
    enum { COLOR_RED, COLOR_GREEN, COLOR_BLUE } color_var; 
    struct { int x_coord, y_coord; } point_var; 
    always_comb begin
        out_status = 8'h0;
        case (in_value)
            4'd0: begin
                current_state = STATE_IDLE;
                packet_info.addr = 8'hAA;
                my_expanded_val = ZERO_EXPAND;
            end
            4'd1: begin
                current_state = STATE_RUNNING;
                packet_info.data = 8'hBB;
                my_expanded_val = expanded_enum_t'(3); 
            end
            default: begin
                current_state = STATE_STOPPED;
                color_var = COLOR_BLUE;
                point_var.x_coord = in_value;
                out_status = packet_info.addr + packet_info.data + color_var + point_var.x_coord;
            end
        endcase
    end
endmodule
module VerilatorAttributes (
    input logic clk_i,
    input logic rst_ni,
    output logic [7:0] data_o
);
    logic (* verilator public *) public_signal;
    logic (* verilator public_flat_rw *) public_flat_rw_signal;
    logic (* verilator public_flat_rd *) public_flat_rd_signal;
    logic (* verilator forceable *) forceable_signal;
    logic (* verilator split_var *) split_var_signal;
    logic (* verilator clk_enable *) clk_enable_signal; 
    logic (* verilator clocker *) clocker_signal;
    logic (* verilator no_clocker *) no_clocker_signal;
    logic (* verilator isolate_assignments *) iso_assign_signal;
    string (* verilator sformat *) sformat_str;
    logic [31:0] (* verilator sc_bv *) sc_bv_data;
    logic /* verilator public_flat_rw */ internal_public_wire;
    always_public internal_public_wire; 
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            public_signal <= 1'b0;
            public_flat_rw_signal <= 8'h0;
            public_flat_rd_signal <= 8'h0;
            forceable_signal <= 1'b0;
            split_var_signal <= 1'b0;
            clk_enable_signal <= 1'b0;
            clocker_signal <= 1'b0;
            no_clocker_signal <= 1'b0;
            iso_assign_signal <= 1'b0;
            sformat_str = "";
            sc_bv_data <= 32'h0;
            internal_public_wire <= 1'b0;
            data_o <= 8'h0;
        end else begin
            public_signal <= ~public_signal;
            public_flat_rw_signal <= {7'b0, public_signal};
            public_flat_rd_signal <= {7'b0, public_signal};
            forceable_signal <= public_signal;
            split_var_signal <= public_signal;
            clk_enable_signal <= public_signal;
            clocker_signal <= public_signal;
            no_clocker_signal <= public_signal;
            iso_assign_signal <= public_signal;
            sformat_str = "AttributeTest";
            sc_bv_data <= {sc_bv_data[30:0], public_signal};
            internal_public_wire <= public_signal;
            data_o <= sc_bv_data[7:0];
        end
    end
endmodule
module LoopAndWait (
    input logic [7:0] data_in,
    output logic [7:0] sum_out
);
    logic [7:0] array_val [0:3];
    logic [7:0] temp_sum;
    int i;
    assign array_val[0] = data_in;
    assign array_val[1] = data_in + 1;
    assign array_val[2] = data_in + 2;
    assign array_val[3] = data_in + 3;
    always_comb begin
        temp_sum = 0;
        i = 0;
        foreach (array_val[idx]) begin : foreach_block
            temp_sum = temp_sum + array_val[idx];
        end
        repeat (2) begin 
            temp_sum = temp_sum + 1;
        end
        sum_out = temp_sum; 
        i = 0;
        do begin : do_while_block
            temp_sum = temp_sum + 1;
            i++;
        end while (i < 2);
        wait(0); 
        wait(data_in > 0); 
        i = 0;
        while (i < 2) begin : while_block 
            temp_sum = temp_sum + 1;
            i++;
        end
        sum_out = temp_sum; 
    end
endmodule
module GenerateBlockExamples (
    input logic [1:0] sel_i,
    output logic [3:0] out_data
);
    generate
        if (sel_i[0]) begin : gen_if_true_branch 
            assign out_data = 4'h1;
        end else begin : gen_if_false_branch 
            assign out_data = 4'h2;
        end
    endgenerate
    generate
        case (sel_i[1])
            1'b0: begin : gen_case_0_branch
                assign out_data[0] = 1'b0;
            end
            1'b1: begin : gen_case_1_branch
                assign out_data[1] = 1'b1;
            end
        endcase
    endgenerate
    generate
        for (genvar i = 0; i < 2; i++) begin : gen_for_loop_name
            logic [3:0] temp_i;
            assign temp_i = i;
            assign out_data[i+2] = temp_i[0];
        end
    endgenerate
    generate
        if (sel_i[0]) 
            if (sel_i[1]) begin : inner_nested_gen_if 
                assign out_data = 4'hC;
            end
    endgenerate
    module SimpleSubmodule(input a, output b);
        assign b = a;
    endmodule
    SimpleSubmodule named_submodule_inst (
        .a(sel_i[0]),
        .b(out_data[3])
    );
endmodule
module TimeAndPackageImports (
    input logic clk,
    output time current_time_out
);
    timeunit 10ns;
    timeprecision 1ns; 
    string sformatf_result;
    logic [63:0] sys_time_val;
    real sys_realtime_val; 
    class MyClassScopeTest;
        import my_package::*; 
        function new();
        endfunction
        function void use_pkg_func();
            int val = my_package::pkg_func(20);
        endfunction
    endclass
    MyClassScopeTest my_class_inst;
    always_ff @(posedge clk) begin
        if (my_class_inst == null) begin
            my_class_inst = new(); 
        end
        my_class_inst.use_pkg_func();
        sformatf_result = $sformatf("Clk state: %0b", clk);
        sys_time_val = $time;
        sys_realtime_val = $realtime;
        current_time_out = $time; 
    end
endmodule
module ClockingBlockExample (
    input logic clk_i,
    input logic data_in_i,
    output logic data_out_o
);
    logic internal_signal;
    logic my_output_err_signal; 
    clocking cb @(posedge clk_i);
        default input #1step output #0; 
        input #10ns data_in_i; 
        output #5ns data_out_o;
        input internal_signal; 
    endclocking
    clocking cb_error @(posedge clk_i);
        default input #1step output #0;
        default input #2ns; 
        output #1step my_output_err_signal; 
    endclocking
    always_ff @(cb) begin
        internal_signal <= data_in_i;
        data_out_o <= internal_signal;
    end
    assign my_output_err_signal = data_in_i;
endmodule
module ClassConstraintAndDot (
    input logic randomize_en,
    output int total_sum_out
);
    class BaseClass;
        int base_val;
        function new();
            base_val = 10;
        endfunction
    endclass
    class DerivedClass extends BaseClass;
        rand int derived_val;
        constraint c_derived { derived_val inside {[0:100]}; } 
        constraint c_sum { derived_val + base_val < 200; } 
        function new(input int x);
            base_val = x; 
            super.new(); 
        endfunction
        function void some_other_func();
            int local_var_in_func;
            local_var_in_func = 1;
            super.new(); 
        endfunction
        function int get_sum();
            return derived_val + base_val;
        endfunction
    endclass
    DerivedClass my_derived_inst;
    int rand_status;
    always_comb begin
        if (my_derived_inst == null) begin
            my_derived_inst = new(5); 
        end
        if (randomize_en) begin
            rand_status = my_derived_inst.randomize(); 
        end else begin
            rand_status = 0;
        end
        total_sum_out = my_derived_inst.get_sum() + rand_status; 
        my_derived_inst.some_other_func(); 
    end
endmodule
module CoverAndRestrict (
    input logic [1:0] val_i,
    output logic out_o
);
    coverpoint val_i { 
        bins zero = {2'b00};
        bins one = {2'b01};
        bins two = {2'b10};
        bins three = {2'b11};
        bins others = default;
    }
    property p_val_is_one;
        @(posedge val_i[0]) restrict (val_i == 2'b01); 
    endproperty
    assert property (p_val_is_one); 
    assign out_o = val_i[0] | val_i[1];
endmodule
