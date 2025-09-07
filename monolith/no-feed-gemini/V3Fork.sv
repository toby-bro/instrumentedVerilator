module BasicForkModule (
    input logic [7:0] in_data_a,
    input logic [7:0] in_data_b,
    output logic [7:0] out_result
);
    logic [7:0] local_var_1; 
    logic [7:0] local_var_2; 
    always_comb begin
        local_var_1 = in_data_a; 
        local_var_2 = in_data_b; 
        out_result = 8'h00;     
        fork 
            local_var_1 = local_var_1 + 1; 
            out_result = local_var_1 + local_var_2; 
        join_none 
    end
endmodule
module DelayedForkModule (
    input logic [7:0] delay_in,
    output logic [7:0] delay_out
);
    logic [7:0] reg_local_a;
    logic [7:0] reg_local_b; 
    always_ff @(posedge delay_in[0]) begin 
        reg_local_a <= delay_in;
        fork 
            reg_local_b <= reg_local_a + 1; 
        join_none
    end
    assign delay_out = reg_local_b;
endmodule
module ClassForkModule (
    input logic enable_in,
    output logic [3:0] class_result_out
);
    class MyDataClass;
        logic [3:0] value;
        function new();
            this.value = 4'h0;
        endfunction
        function void increment(logic [3:0] add_val);
            this.value = this.value + add_val;
        endfunction
    endclass
    MyDataClass my_handle; 
    logic [3:0] temp_val;
    task automatic modify_handle_task(MyDataClass captured_handle, input logic [3:0] param_val);
        captured_handle.increment(param_val); 
    endtask
    always_comb begin
        class_result_out = 4'h0; 
        if (enable_in) begin
            my_handle = new(); 
            temp_val = 4'h5;
            fork
                modify_handle_task(my_handle, temp_val);
                class_result_out = my_handle.value; 
            join_none
        end
    end
endmodule
module NestedForkModule (
    input logic [7:0] nesting_level_in,
    output logic [7:0] final_val_out
);
    logic [7:0] shared_val; 
    logic [7:0] temp_val;   
    always_comb begin
        shared_val = nesting_level_in;
        temp_val = 8'h00;
        final_val_out = 8'h00;
        fork 
            logic [7:0] outer_local_var = shared_val + 1;
            temp_val = outer_local_var; 
            fork 
                logic [7:0] inner_local_var = outer_local_var + 2;
                final_val_out = inner_local_var; 
            join_none 
        join_none
    end
endmodule
module InitializedForkModule (
    input logic init_val_a,
    input logic init_val_b,
    output logic [1:0] combined_out
);
    always_comb begin
        combined_out = 2'b00;
        fork (
            int declared_var_1 = init_val_a ? 10 : 0; 
            logic [0:0] declared_var_2; 
            declared_var_2 = init_val_b; 
        )
            combined_out[0] = declared_var_1[0];
            combined_out[1] = declared_var_2;
        join_any 
    end
endmodule
module EventAndLifetimeModule (
    input logic trigger_in,
    output logic status_out
);
    event my_event; 
    logic local_dynamic_var; 
    static logic static_var; 
    always_comb begin
        status_out = 1'b0;
        local_dynamic_var = 1'b0;
        static_var = 1'b1; 
        if (trigger_in) begin
            fork 
                -> my_event; 
                status_out = local_dynamic_var; 
                static_var = static_var + 1'b0;
            join_none
        end
    end
endmodule
module TaskInForkModule (
    input logic [7:0] in_task_val,
    output logic [7:0] out_task_res
);
    logic [7:0] module_local_var; 
    task automatic my_local_task(input logic [7:0] task_in_val);
        logic [7:0] task_auto_var; 
        task_auto_var = task_in_val + module_local_var; 
        out_task_res = task_auto_var;
    endtask
    always_comb begin
        module_local_var = in_task_val;
        out_task_res = 8'h00;
        fork
            my_local_task(in_task_val + 1);
        join_none
    end
endmodule
module ComplexInitForkModule (
    input logic [7:0] initial_value,
    output logic [7:0] final_sum
);
    logic [7:0] fork_outer_var; 
    always_comb begin
        fork_outer_var = initial_value;
        final_sum = 8'h00;
        fork (
            int declared_var_1 = 10;                     
            logic [7:0] declared_var_2;                  
            declared_var_2 = fork_outer_var + declared_var_1; 
        )
            final_sum = declared_var_1 + declared_var_2;
        join_none
    end
endmodule
module BeginForkModule (
    input logic [0:0] trigger,
    input logic [7:0] data_in,
    output logic [7:0] data_out
);
    logic [7:0] local_state; 
    always_comb begin
        data_out = 8'h00;
        local_state = data_in;
        if (trigger) begin 
            local_state <= data_in + 1; 
            data_out = local_state; 
        end
    end
endmodule
module MultiCaptureModule (
    input logic [3:0] in_a,
    input logic [3:0] in_b,
    input logic [3:0] in_c,
    output logic [3:0] out_sum
);
    logic [3:0] var_x;
    logic [3:0] var_y;
    logic [3:0] var_z;
    always_comb begin
        var_x = in_a;
        var_y = in_b;
        var_z = in_c;
        out_sum = 4'h0;
        fork
            var_x = var_x + 1;
            var_y = var_y + 2;
            var_z = var_z + 3;
            out_sum = var_x + var_y + var_z;
        join_none
    end
endmodule
