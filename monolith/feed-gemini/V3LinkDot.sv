`default_nettype wire
package my_types_pkg;
    typedef enum {RED, GREEN, BLUE} color_e;
endpackage
module ModuleBasic(
    input logic [7:0] in_data,
    output logic [7:0] out_result
);
    logic [7:0] internal_reg;
    logic [7:0] internal_logic_main;
    localparam int LP_VALUE = 10;
    parameter P_WIDTH = 8;
    assign internal_logic_main = in_data + LP_VALUE;
    begin : named_scope_block
        logic [P_WIDTH-1:0] block_reg;
        localparam int BLOCK_LP = LP_VALUE * 2;
        assign block_reg = internal_logic_main - BLOCK_LP;
        logic [P_WIDTH-1:0] local_shadowed_var;
        assign local_shadowed_var = block_reg;
        assign implicit_wire_a = block_reg + 1;
    end : named_scope_block
    logic [P_WIDTH-1:0] local_shadowed_var;
    assign local_shadowed_var = internal_reg;
    wire driver_w, load_w;
    tranif0 (driver_w, load_w, 1'b1);
    assign another_implicit = 8'hFF;
    logic [7:0] block_signal_access;
    always_comb block_signal_access = named_scope_block.block_reg;
    wire my_pullup_wire;
    pullup (my_pullup_wire);
    always_comb begin
        out_result = internal_logic_main + 1;
    end
endmodule
interface BasicInterface #(parameter DATA_WIDTH = 8);
    logic [DATA_WIDTH-1:0] data_internal;
    logic valid_internal;
    logic ready_internal;
    logic [DATA_WIDTH-1:0] data_port;
    logic valid_port;
    logic ready_port;
    modport master (
        output data_port,
        output valid_port,
        input ready_port
    );
    modport slave (
        input data_port,
        input valid_port,
        output ready_port
    );
    function void set_data(input logic [DATA_WIDTH-1:0] new_data);
        data_internal = new_data;
        data_port = new_data;
    endfunction
    task get_data(output logic [DATA_WIDTH-1:0] current_data);
        current_data = data_internal;
    endtask
    assign valid_port = valid_internal;
    assign ready_internal = ready_port;
endinterface
module ModuleInterface (
    input logic clk,
    input logic reset_n,
    virtual BasicInterface vif_master_port, 
    virtual BasicInterface vif_slave_port,  
    output logic [7:0] out_val
);
    logic [7:0] data_from_slave;
    logic slave_ready_sig;
    assign slave_ready_sig = vif_slave_port.ready_port;
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            data_from_slave <= 8'h00;
        end else if (vif_slave_port.valid_port) begin
            data_from_slave <= vif_slave_port.data_port;
        end
    end
    always_comb begin
        vif_master_port.set_data(data_from_slave + 1); 
        vif_master_port.valid_port = 1'b1;
        vif_master_port.get_data(out_val); 
    end
    virtual BasicInterface vif_unassigned; 
    BasicInterface #(16) parameterized_if_inst ();
    always_comb parameterized_if_inst.set_data(16'h1234);
endmodule
import my_types_pkg::*;
virtual class BaseClass #(parameter BP_VAL = 1);
    rand int base_var;
    pure virtual function int get_value();
    pure constraint c_base;
endclass
class DerivedClass #(parameter DP_VAL = 1) extends BaseClass #(DP_VAL + 1);
    rand int derived_var;
    color_e my_color;
    constraint c_base { base_var inside {[0:100]}; }
    function new();
        super.new();
    endfunction
    virtual function int get_value();
        return base_var + derived_var + DP_VAL;
    endfunction
    constraint c_derived { derived_var > base_var; }
    function void my_randomize_method();
        this.randomize() with {
            base_var == 50;
            derived_var > 0;
        };
    endfunction
    function void set_modes();
        this.base_var.rand_mode(0);
        this.c_derived.constraint_mode(0);
    endfunction
    function color_e get_color();
        return RED;
    endfunction
    protected static int s_class_counter = 0;
    function void increment_counter();
        s_class_counter++;
    endfunction
endclass
class DerivedClass2 extends BaseClass;
    rand int derived_var_2;
    constraint c_base { base_var inside {[0:100]}; }
    function new();
    endfunction
    virtual function int get_value();
        return base_var + derived_var_2 + BP_VAL;
    endfunction
endclass
module ModuleClasses (
    input logic clk,
    output int out_sum
);
    DerivedClass my_obj;
    DerivedClass2 my_obj2;
    always_ff @(posedge clk) begin
        if (my_obj == null) begin
            my_obj = new();
            my_obj.randomize();
            my_obj.my_randomize_method();
        end
        if (my_obj2 == null) begin
            my_obj2 = new();
        end
        out_sum = my_obj.get_value() + my_obj2.derived_var_2;
        my_obj.set_modes();
        my_obj.increment_counter();
    end
    DerivedClass #(10) my_param_obj;
    int temp_val;
    always_comb begin
        temp_val = my_param_obj.get_value();
        case(my_obj.get_color())
            RED: temp_val += 1;
            GREEN: temp_val += 2;
            BLUE: temp_val += 3;
            default: temp_val += 0;
        endcase
    end
    parameter int MyParamValue = 1;
    typedef DerivedClass #(MyParamValue) SpecificDerivedType;
    SpecificDerivedType specific_obj;
endmodule
module ModuleHierarchy (
    input logic [7:0] in_h_data,
    output logic [7:0] out_h_result
);
    logic [7:0] local_h_var;
    logic [7:0] gen_if_var_internal;
    logic [7:0] gen_for_var_overall;
    logic [7:0] foreach_sum;
    logic [7:0] final_output_val;
    generate if (1) begin : gen_if_block
        logic [7:0] gen_var;
        assign gen_var = in_h_data + 1;
        assign local_h_var = gen_var;
        assign gen_if_var_internal = gen_var;
    end else begin : gen_else_block
        logic [7:0] gen_var;
        assign gen_var = in_h_data - 1;
        assign local_h_var = gen_var;
        assign gen_if_var_internal = gen_var;
    end
    endgenerate
    genvar i;
    generate
        for (i = 0; i < 2; i++) begin : gen_for_block
            logic [7:0] loop_var_local;
            if (i == 0) begin : inner_block
                localparam int INNER_LP = 5;
                assign loop_var_local = local_h_var + i;
                assign gen_for_var_overall = loop_var_local + INNER_LP;
            end else begin
                assign loop_var_local = local_h_var + i;
            end
        end
    endgenerate
    logic [7:0] accessed_gen_var;
    always_comb begin
        accessed_gen_var = gen_if_block.gen_var;
    end
    logic [7:0] array_data [4];
    always_comb begin
        foreach (array_data[idx]) begin : foreach_index_block
            array_data[idx] = idx;
        end
        foreach_sum = 0;
        foreach (array_data[j]) begin
            foreach_sum += array_data[j];
        end
    end
    always_comb begin
        final_output_val = 8'h0;
        if (gen_if_var_internal != 8'h0) final_output_val = gen_if_var_internal;
        else if (gen_for_var_overall != 8'h0) final_output_val = gen_for_var_overall;
        else if (foreach_sum != 8'h0) final_output_val = foreach_sum;
        out_h_result = final_output_val;
    end
    task disable_test_task();
        begin : disable_target_block
            static int val = 0;
            disable disable_target_block;
            val = 1;
        end
    endtask
    parameter int P4_VAL = 1;
    typedef logic [P4_VAL-1:0] MyDynamicType;
    MyDynamicType my_dynamic_var;
    assign my_dynamic_var = in_h_data;
endmodule
module ModuleAdvanced(
    input logic enable_clk,
    input logic [3:0] in_data_adv,
    output int out_status
);
    typedef enum {STATE_IDLE, STATE_RUNNING, STATE_DONE = 20} FSM_STATE_T;
    FSM_STATE_T current_state;
    always_comb begin
        current_state = STATE_IDLE;
        if (in_data_adv > 5) begin
            current_state = STATE_RUNNING;
        end else begin
            current_state = STATE_DONE;
        end
    end
    logic [3:0] cb_in_data_wire;
    int cb_out_status_internal;
    assign cb_in_data_wire = in_data_adv;
    clocking my_cb @(posedge enable_clk);
        input in_data_adv = cb_in_data_wire;
        output out_status_cb = cb_out_status_internal;
    endclocking
    always_ff @(my_cb) begin
        my_cb.out_status_cb <= my_cb.in_data_adv;
    end
    parameter type DATA_TYPE_PARAM = logic [7:0];
    DATA_TYPE_PARAM my_typed_var;
    import "DPI-C" function int dpi_get_value(input int arg);
    function void dpi_set_status_sv(input int status_val);
    endfunction
    export "DPI-C" function dpi_set_status_sv;
    function int get_converted_value();
        return dpi_get_value(in_data_adv);
    endfunction
    task set_exported_status();
        dpi_set_status_sv(current_state);
    endtask
    always_comb begin
        out_status = get_converted_value();
    end
    typedef FSM_STATE_T StateType;
    function int get_state_size();
        return $bits(StateType);
    endfunction
    typedef logic [7:0] PackedByte_t;
    PackedByte_t my_packed_array [2:0];
    assign my_packed_array[0] = 8'h11;
    assign my_packed_array[1][3:0] = 4'h2;
    assign my_packed_array[2][7] = 1'b1;
    typedef struct packed {
        logic [3:0] field1;
        logic [3:0] field2;
    } my_struct_t;
    my_struct_t my_struct_var;
    assign my_struct_var.field1 = in_data_adv;
endmodule
module LowerModule (
    input logic [7:0] lower_in,
    output logic [7:0] lower_out
);
    assign lower_out = lower_in * 2;
endmodule
module ModuleInlineTest (
    input logic [7:0] inline_test_in,
    output logic [7:0] inline_test_out
);
    LowerModule lm_inst (
        .lower_in(inline_test_in),
        .lower_out(inline_test_out)
    );
endmodule
module ModuleUnlinkedRefTest (
    input logic [7:0] ureft_in,
    output logic [7:0] ureft_out
);
    parameter type UREF_PARAM_TYPE = int;
    UREF_PARAM_TYPE uref_var = ureft_in;
    assign ureft_out = uref_var;
endmodule
module ModuleDefparamTarget(input int in_val, output int out_val);
    parameter PARAM_DP = 10;
    assign out_val = in_val + PARAM_DP;
endmodule
module ModuleDefparam (
    input int in_dp_data,
    output int out_dp_result
);
    ModuleDefparamTarget inst_dp (
        .in_val(in_dp_data),
        .out_val(out_dp_result)
    );
    defparam inst_dp.PARAM_DP = 20;
endmodule
module GlobalClockingModule(
    input logic clk,
    input logic global_in,
    output logic global_out
);
    clocking global_cb @(posedge clk);
        input global_in;
        output global_out;
    endclocking
    always_ff @(posedge clk) begin
        global_cb.global_out <= global_cb.global_in;
    end
endmodule
interface TopInterface(input bit clk_if);
    logic data_signal;
    assign data_signal = clk_if;
endinterface
module ModuleTopInterface (TopInterface top_if_port, output int result_if);
    assign result_if = top_if_port.data_signal;
endmodule
module ModuleDuplicatePortTarget (
    input logic in1,
    input logic in2,
    output logic out_and
);
    assign out_and = in1 & in2;
endmodule
module ModuleDuplicatePortTest (
    input logic test_in,
    output logic test_out
);
    ModuleDuplicatePortTarget mdt_inst (
        .in1(test_in),
        .in2(test_in),
        .out_and(test_out)
    );
endmodule
module DummyTop (
    input logic clk,
    input logic reset_n,
    input logic [7:0] data_in,
    output logic [7:0] data_out
);
    logic [7:0] internal_data_mb;
    ModuleBasic mb_inst (
        .in_data(data_in),
        .out_result(internal_data_mb)
    );
    logic [7:0] if_out;
    BasicInterface shared_if_inst(); 
    ModuleInterface mif_inst (
        .clk(clk),
        .reset_n(reset_n),
        .vif_master_port(shared_if_inst), 
        .vif_slave_port(shared_if_inst),  
        .out_val(if_out)
    );
    int class_sum;
    ModuleClasses mc_inst (
        .clk(clk),
        .out_sum(class_sum)
    );
    logic [7:0] hierarchy_out;
    ModuleHierarchy mh_inst (
        .in_h_data(data_in),
        .out_h_result(hierarchy_out)
    );
    int adv_status;
    ModuleAdvanced ma_inst (
        .enable_clk(clk),
        .in_data_adv(data_in[3:0]),
        .out_status(adv_status)
    );
    logic [7:0] inline_out;
    ModuleInlineTest mit_inst (
        .inline_test_in(data_in),
        .inline_test_out(inline_out)
    );
    logic [7:0] uref_out;
    ModuleUnlinkedRefTest murt_inst (
        .ureft_in(data_in),
        .ureft_out(uref_out)
    );
    int dp_val;
    ModuleDefparam mdp_inst (
        .in_dp_data(data_in[7:0]),
        .out_dp_result(dp_val)
    );
    logic gcb_global_out;
    GlobalClockingModule gcb_inst (
        .clk(clk),
        .global_in(data_in[0]),
        .global_out(gcb_global_out)
    );
    TopInterface top_if_inst(.clk_if(clk));
    int top_if_result;
    ModuleTopInterface mti_inst (
        .top_if_port(top_if_inst),
        .result_if(top_if_result)
    );
    logic dup_output_from_mdpt;
    ModuleDuplicatePortTest mdpt_inst (
        .test_in(data_in[0]),
        .test_out(dup_output_from_mdpt)
    );
    always_comb begin
        data_out = internal_data_mb;
        data_out[0] = gcb_global_out;
        data_out[1] = dup_output_from_mdpt;
    end
endmodule
