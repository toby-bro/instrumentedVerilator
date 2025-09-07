interface MyInterface (input bit clk);
    logic [7:0] data;
    modport master (output data);
    modport slave (input data);
    function void import_func();
    function void export_func();
endinterface
class BaseClass;
    rand int base_prop;
    constraint base_c {base_prop > 0;};
    virtual function int get_value();
        return base_prop;
    endfunction
endclass
class DerivedClass extends BaseClass;
    rand int derived_prop;
    constraint derived_c {derived_prop inside {[10:20]};}
    virtual function int get_value();
        return base_prop + derived_prop;
    endfunction
endclass
import "DPI-C" pure function int dpi_add (input int a, input int b);
export "DPI-C" function void dpi_log (input string message);
module BasicLogicAndOps (
    input logic [7:0] i_a,
    input signed int i_b,
    input bit i_clk,
    input logic i_reset_n,
    output logic [15:0] o_result,
    output int o_state_val
);
    logic [15:0] internal_reg;
    logic [15:0] next_internal_reg;
    logic [3:0] case_sel;
    logic [15:0] case_out_wire;
    wire (pullup) pu_wire;
    wire (pulldown) pd_wire;
    const int MY_CONST = 123;
    always_comb begin
        next_internal_reg = (i_a + i_b) * 2;
        next_internal_reg = next_internal_reg / 4;
        next_internal_reg = next_internal_reg % MY_CONST;
        next_internal_reg = ~next_internal_reg;
        next_internal_reg = -next_internal_reg;
        o_result = (i_reset_n) ? 16'b0 : next_internal_reg;
        case_sel = i_a[3:0];
        if (i_b > 0) begin
            case_sel[0] = i_a[7];
        end else begin
            case_sel[1] = i_a[6];
        end
        unique casez (case_sel)
            4'b000?: case_out_wire = MY_CONST + 1;
            4'b001?: case_out_wire = MY_CONST + 2;
            default: case_out_wire = MY_CONST + 3;
        endcase
        case (i_a[1:0])
            2'b00: case_out_wire = case_out_wire + 1;
            2'b01: case_out_wire = case_out_wire + 2;
            2'b10: case_out_wire = case_out_wire + 3;
            2'b11: case_out_wire = case_out_wire + 4;
        endcase
        o_state_val = internal_reg[7:0] + MY_CONST;
    end
    always_ff @(posedge i_clk or negedge i_reset_n) begin
        if (!i_reset_n) begin
            internal_reg = 16'b0;
        end else begin
            internal_reg = next_internal_reg;
        end
    end
    always_latch if (i_clk) begin
        if (i_a > 10) begin
            pu_wire = 1'b0;
            pd_wire = 1'b1;
        end
    end
endmodule
module AdvancedTypesAndFlow (
    input bit i_enable,
    input int i_addr,
    output logic [31:0] o_data_out,
    output bit o_status
);
    typedef struct packed {
        logic [7:0] field_a;
        int         field_b;
    } my_packed_struct_t;
    typedef struct unpacked {
        logic [7:0] field_c;
        real        field_d;
    } my_unpacked_struct_t;
    typedef my_packed_struct_t packed_array_t [3:0];
    typedef int unpacked_array_t [2];
    typedef int dynamic_array_t [];
    typedef real queue_t [$];
    typedef string assoc_array_t [string];
    typedef bit wildcard_array_t [*];
    typedef int unsized_array_t [];
    packed_array_t pa;
    unpacked_array_t upa;
    dynamic_array_t da;
    queue_t q;
    assoc_array_t aa;
    wildcard_array_t wa;
    unsized_array_t usa;
    my_packed_struct_t current_packed_struct;
    my_unpacked_struct_t current_unpacked_struct;
    typedef enum {STATE_IDLE, STATE_BUSY, STATE_DONE} fsm_state_e;
    fsm_state_e current_state;
    always_comb begin
        current_packed_struct.field_a = i_addr[7:0];
        current_packed_struct.field_b = i_addr;
        current_unpacked_struct.field_c = i_addr[7:0];
        current_unpacked_struct.field_d = $itor(i_addr);
        o_data_out = current_packed_struct.field_b;
        o_status = current_unpacked_struct.field_d > 0.5;
        if (i_addr inside {[0:10], [100:200]}) begin
            current_state = STATE_BUSY;
        end else begin
            current_state = STATE_IDLE;
        end
    end
    always_ff @(posedge i_enable) begin
        automatic int temp_idx;
        automatic int loop_val = 0;
        begin : my_flow_block
            da = new [4];
            q = new [10];
            if (i_enable) begin
                da.push_back(i_addr);
                q.push_back($itor(i_addr));
                if (da.size() > 2) begin
                    temp_idx = da.pop_front();
                end
            end
            while (loop_val < da.size()) begin : loop_block
                aa["key"] = $sformatf("Value_%0d", da[loop_val]);
                loop_val++;
            end
            fork : my_fork_block
                automatic int fork_var_1 = 0;
                if (i_addr == 5) begin : jump_target_block
                    fork_var_1 = 1;
                    disable my_flow_block;
                end
            join_none
            if (aa.exists("key")) begin
                o_data_out = aa.find("key") + 1;
            end else begin
                o_data_out = 0;
            end
        end
    end
endmodule
module ClassInterfaceDPI (
    input int i_input_val,
    input bit i_dpi_enable,
    input bit i_clk_dpi,
    output int o_output_val,
    output int o_dpi_result,
    output int o_class_cond_val
);
    MyInterface iface_inst (i_clk_dpi);
    DerivedClass my_obj_derived;
    BaseClass my_obj_base;
    BaseClass conditional_obj;
    event my_event;
    clocking cb @(posedge i_clk_dpi);
        default input #1step output #0;
        input i_input_val;
        output o_output_val;
    endclocking
    always_comb begin
        if (i_input_val > 100) begin
            if (my_obj_derived == null) begin
                my_obj_derived = new();
                if (my_obj_derived.randomize() == 0) begin
                end
            end
            o_output_val = my_obj_derived.get_value();
        end else begin
            if (my_obj_derived != null) begin
                my_obj_derived = null;
            end
            o_output_val = 0;
        end
        if (my_obj_base == null) begin
            my_obj_base = new();
        end
        conditional_obj = (i_input_val > 50) ? my_obj_derived : my_obj_base;
        o_class_cond_val = (conditional_obj != null) ? conditional_obj.get_value() : 0;
    end
    always_ff @(cb) begin
        if (i_dpi_enable) begin
            o_dpi_result = dpi_add(i_input_val, 5);
            dpi_log($sformatf("DPI call with input: %0d", i_input_val));
        end else begin
            o_dpi_result = 0;
        end
        ->my_event;
    end
    assign iface_inst.master.data = o_output_val[7:0];
    assign o_output_val[7:0] = iface_inst.slave.data;
endmodule
module HierarchyAndControl (
    input bit i_cond,
    input int i_data_in,
    input int i_loop_max,
    input int i_break_val,
    input int i_continue_val,
    output int o_data_out_final,
    output int o_loop_sum
);
    int local_data;
    int loop_counter;
    int temp_sum;
    always_comb begin : main_control_block
        local_data = i_data_in;
        o_data_out_final = 0;
        o_loop_sum = 0;
        temp_sum = 0;
        loop_counter = 0; 
        while (loop_counter < i_loop_max) begin : loop_block
            if (loop_counter == i_continue_val) begin
                loop_counter++;
                continue;
            end
            temp_sum += loop_counter;
            if (loop_counter == i_break_val) begin
                break;
            end
            loop_counter++;
        end
        o_loop_sum = temp_sum;
        fork : my_fork_join_block
            automatic int fork_var_1 = 0;
            if (i_cond) begin
                fork_var_1 = local_data + 1;
            end
        join
        fork : my_fork_join_any_block
            automatic int fork_var_2 = 0;
            if (!i_cond) begin
                fork_var_2 = local_data + 2;
            end
        join_any
        fork : my_fork_join_none_block
            automatic int fork_var_3 = 0;
            if (i_data_in > 10) begin
                fork_var_3 = local_data + 3;
                disable main_control_block;
            end
        join_none
        assign o_data_out_final = this.i_data_in + this.o_loop_sum;
    end
    task my_task(input int val, output int res);
        int local_res = 0;
        begin : task_body_block
            local_res = val * 2;
            if (val > 100) begin
                return;
            end
            local_res += 10;
        end
        res = local_res;
    endtask
    always_ff @(posedge i_cond) begin
        automatic int task_out;
        my_task(i_data_in, task_out);
        o_data_out_final = task_out;
    end
endmodule
