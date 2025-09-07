module BasicVarElimModule (
    input logic [7:0] in_data_a,
    input logic [7:0] in_data_b,
    output logic [7:0] out_result_sum,
    output logic out_flag_eq
);
    logic [7:0] local_var_used;
    logic [7:0] local_var_unused_1; 
    logic [7:0] local_var_temp_test; 
    logic [7:0] local_var_io; 
    logic [7:0] local_var_public; 
    logic [7:0] local_var_assigned_only; 
    always_comb begin
        local_var_used = in_data_a + in_data_b;
        out_result_sum = local_var_used; 
        local_var_unused_1 = 8'd10; 
        local_var_temp_test = in_data_a * 2; 
        out_flag_eq = (in_data_a == in_data_b); 
        local_var_assigned_only = in_data_b - in_data_a; 
    end
    localparam int PUBLIC_CONSTANT = 100;
    assign local_var_public = PUBLIC_CONSTANT; 
    assign local_var_io = in_data_a; 
    generate
        if (1'b0) begin : unused_scope_block
            logic [3:0] dead_scope_var; 
            dead_scope_var = 4'd0;
        end
    endgenerate
endmodule
module DataTypeElimModule (
    input logic [15:0] input_val,
    output logic [15:0] output_sum
);
    typedef enum logic [1:0] {
        STATE_IDLE,
        STATE_RUNNING,
        STATE_PAUSED = 2'b10,
        STATE_STOPPED
    } my_fsm_state_t;
    my_fsm_state_t current_state;
    my_fsm_state_t next_state_unused; 
    my_fsm_state_t next_state_used;
    typedef struct packed {
        logic [7:0] addr;
        logic [7:0] data;
    } packet_t;
    packet_t tx_packet;
    packet_t rx_packet_unused; 
    typedef union {
        int ival;
        real rval;
    } data_union_t;
    data_union_t my_union;
    typedef struct packed {
        logic [3:0] packed_val;
    } public_packed_struct_t;
    typedef struct {
        logic [3:0] unpacked_val;
    } public_unpacked_struct_t;
    typedef logic [31:0] unused_data_t;
    unused_data_t some_unused_var;
    always_comb begin
        if (input_val[0]) begin
            current_state = STATE_RUNNING;
        end else begin
            current_state = STATE_IDLE;
        end
        next_state_used = STATE_PAUSED; 
        tx_packet.addr = input_val[15:8];
        tx_packet.data = input_val[7:0];
        my_union.ival = input_val;
        output_sum = tx_packet.addr + tx_packet.data + my_union.ival;
    end
    parameter int MAX_DEPTH = 32;
    public_packed_struct_t public_packed_instance;
    public_unpacked_struct_t public_unpacked_instance;
    assign public_packed_instance.packed_val = input_val[3:0];
    assign public_unpacked_instance.unpacked_val = input_val[7:4];
endmodule
module ClassAndScopeElimModule (
    input logic clk_in,
    input logic rst_n_in,
    output logic [3:0] class_result
);
    class BaseClass;
        rand int m_base_val;
        function new();
            m_base_val = 10;
        endfunction
        virtual function int get_val(); 
            return m_base_val;
        endfunction
    endclass
    class DerivedClass extends BaseClass;
        rand int m_derived_offset;
        function new();
            super.new();
            m_derived_offset = 5;
        endfunction
        virtual function int get_val(); 
            return super.get_val() + m_derived_offset;
        endfunction
        function void dead_method(); 
            int unused_local;
            unused_local = 0;
        endfunction
    endclass
    class UnusedClass;
        int dummy_var;
    endclass
    BaseClass base_inst;
    DerivedClass derived_inst;
    UnusedClass unused_inst; 
    int base_val_sum;
    int derived_val_sum;
    always_ff @(posedge clk_in or negedge rst_n_in) begin : class_proc_block
        if (!rst_n_in) begin : reset_scope
            base_inst = null;
            derived_inst = null;
            base_val_sum = 0;
            derived_val_sum = 0;
        end else begin : active_scope
            if (base_inst == null) begin
                base_inst = new(); 
            end
            if (derived_inst == null) begin
                derived_inst = new();
            end
            base_val_sum = base_inst.get_val();
            derived_val_sum = derived_inst.get_val();
            class_result = base_val_sum[3:0] + derived_val_sum[3:0];
        end
    end
    always_comb begin : another_unused_scope
        logic [7:0] dead_var_in_scope; 
        if (1'b0) begin : truly_dead_scope
            dead_var_in_scope = 8'hFF;
        end
    end
endmodule
module InterfaceModportModule (
    input logic i_clk,
    input logic i_rst_n,
    output logic o_data_out
);
    interface my_interface (input logic clk);
        logic [7:0] data;
        logic enable;
        modport master (
            output data,
            output enable
        );
        modport slave (
            input data,
            input enable
        );
        modport dead_modport (); 
        function int get_scaled_data(int scale_factor);
            return data * scale_factor;
        endfunction
    endinterface
    my_interface if_master_inst (i_clk); 
    my_interface if_unused_inst (i_clk);
    my_sub_module_master u_master_inst (
        .clk(i_clk),
        .rst_n(i_rst_n),
        .port(if_master_inst.master)
    );
    my_sub_module_no_use u_no_use_inst (
        .clk(i_clk),
        .port(if_unused_inst)
    );
    my_interface if_var;
    assign if_var = if_master_inst; 
    assign o_data_out = if_master_inst.data[0];
    logic dummy_enable;
    always_comb begin
        dummy_enable = i_clk & i_rst_n;
    end
    module my_sub_module_master (
        input logic clk,
        input logic rst_n,
        my_interface.master port
    );
        logic [7:0] internal_data;
        logic internal_enable;
        always_ff @(posedge clk or negedge rst_n) begin
            if (!rst_n) begin
                internal_data <= 8'h00;
                internal_enable <= 1'b0;
            end else begin
                internal_data <= internal_data + 1;
                internal_enable <= ~internal_enable;
            end
        end
        assign port.data = internal_data;
        assign port.enable = internal_enable;
        logic [15:0] scaled_val;
        assign scaled_val = port.get_scaled_data(2);
    endmodule
    module my_sub_module_no_use (
        input logic clk,
        my_interface port
    );
        logic dummy_signal;
        always_comb begin
            dummy_signal = clk;
        end
    endmodule
endmodule
module FuncTaskDPIModule (
    input logic [7:0] in_operand_a,
    input logic [7:0] in_operand_b,
    output logic [7:0] out_func_result,
    output logic [7:0] out_task_result
);
    function automatic logic [7:0] my_sum_func(logic [7:0] val_a, logic [7:0] val_b);
        return val_a + val_b;
    endfunction
    task automatic my_mult_task(input logic [7:0] val_a, input logic [7:0] val_b, output logic [7:0] result);
        result = val_a * val_b;
    endtask
    import "DPI-C" function int dpi_add(int a, int b);
    import "DPI-C" function void dpi_void_func(); 
    int dpi_sum_val;
    class Calculator;
        int internal_val;
        function new();
            internal_val = 0;
        endfunction
        function int add_method(int a, int b);
            internal_val = a + b;
            return internal_val;
        endfunction
        function void unused_method(); 
            int local_dead_var;
            local_dead_var = 0;
        endfunction
    endclass
    Calculator calc_inst;
    always_comb begin
        out_func_result = my_sum_func(in_operand_a, in_operand_b);
        my_mult_task(in_operand_a, in_operand_b, out_task_result);
        dpi_sum_val = dpi_add(in_operand_a, in_operand_b);
        if (calc_inst == null) begin
            calc_inst = new();
        end
        out_func_result = out_func_result + calc_inst.add_method(dpi_sum_val, 1); 
    end
    typedef enum {RED, GREEN, BLUE} Color_t;
    Color_t current_color = RED;
    function automatic int get_color_val(Color_t color);
        case (color)
            RED: return 0;
            GREEN: return 1;
            BLUE: return 2;
        endcase
    endfunction
    always_comb begin
        out_task_result = out_task_result + get_color_val(current_color);
        current_color = GREEN; 
    end
endmodule
module ComplexAssignmentLoopModule (
    input logic [7:0] in_start_val,
    input logic [7:0] in_loop_count,
    output logic [15:0] out_accum_sum,
    output logic out_final_flag
);
    logic [7:0] loop_var_i; 
    logic [15:0] accumulator;
    logic [7:0] temp_var_1, temp_var_2;
    logic [7:0] dead_assign_lhs; 
    always_comb begin
        temp_var_1 = in_start_val + 1;
        temp_var_2 = (temp_var_1 > 10) ? temp_var_1 : in_start_val; 
        accumulator = 0; 
    end
    always_comb begin
        for (loop_var_i = 0; loop_var_i < in_loop_count; loop_var_i = loop_var_i + 1) begin
            accumulator = accumulator + (in_start_val + loop_var_i);
        end
    end
    always_comb begin
        dead_assign_lhs = in_start_val + in_loop_count; 
    end
    logic nested_assign_target;
    logic nested_assign_temp;
    logic nested_assign_val;
    assign nested_assign_val = 1'b1;
    always_comb begin
        if (in_start_val > 5) begin
            nested_assign_temp = nested_assign_val; 
            nested_assign_target = nested_assign_temp; 
        end else begin
            nested_assign_target = 1'b0;
        end
    end
    assign out_accum_sum = accumulator;
    assign out_final_flag = nested_assign_target;
    clocking my_clk_block @(posedge in_start_val[0]);
        input in_loop_count;
        output out_final_flag;
    endclocking
endmodule
module DeepHierarchyDeadCellModule (
    input logic clk,
    input logic rst,
    output logic [2:0] out_counter
);
    module sub_counter (
        input logic i_clk,
        input logic i_rst,
        input logic [2:0] i_increment,
        output logic [2:0] o_count
    );
        reg [2:0] count_reg;
        always_ff @(posedge i_clk or posedge i_rst) begin
            if (i_rst)
                count_reg <= 3'b0;
            else
                count_reg <= count_reg + i_increment;
        end
        assign o_count = count_reg;
    endmodule
    sub_counter u_counter_inst (
        .i_clk(clk),
        .i_rst(rst),
        .i_increment(3'd1),
        .o_count(out_counter)
    );
    module unused_module_top (
        input logic unused_in,
        output logic unused_out
    );
        assign unused_out = unused_in;
    endmodule
    generate
        if (1'b0) begin : gen_dead_instance
            sub_counter u_dead_counter_inst ( 
                .i_clk(clk),
                .i_rst(rst),
                .i_increment(3'd0),
                .o_count() 
            );
        end
    endgenerate
    generate
        if (1'b1) begin : gen_live_block
            module internal_unused_module (
                input logic internal_in,
                output logic internal_out
            );
                assign internal_out = internal_in;
                logic [7:0] internal_dead_var; 
            endmodule
        end
    endgenerate
endmodule
