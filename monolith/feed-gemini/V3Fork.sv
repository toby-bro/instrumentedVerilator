module Module_ForkLocalVar (
    input bit clk,
    input logic [7:0] in_data,
    output logic [7:0] out_sum_local
);
    logic [7:0] local_capture_var;
    logic [7:0] local_auto_var;
    event my_local_event;
    always @(posedge clk) begin : comb_block_for_fork
        automatic int fork_outer_var = in_data + 5;
        local_capture_var = fork_outer_var;
        local_auto_var = 0;
        fork
            automatic int fork_local_x = 1;
            automatic int fork_local_y = fork_local_x + local_capture_var;
            local_capture_var = fork_outer_var * 2;
            local_auto_var = fork_local_y;
            call_my_task(local_capture_var, local_auto_var, my_local_event);
            local_capture_var = local_auto_var + fork_local_x;
            -> my_local_event;
        join_none
        out_sum_local = local_capture_var + local_auto_var;
    end
    task automatic call_my_task;
        input int a;
        output int b;
        output event e;
        b = a + 10;
    endtask
endmodule
module Module_ClassHandle (
    input bit clk,
    input logic create_handle,
    output logic [7:0] class_data_out
);
    class MyDataClass;
        logic [7:0] val;
        function new(logic [7:0] initial_val);
            this.val = initial_val;
        endfunction
        function void set_val(logic [7:0] new_val);
            this.val = new_val;
        endfunction
    endclass
    MyDataClass my_handle;
    logic handle_created_once = 1'b0;
    always @(posedge clk) begin : class_manip_block
        class_data_out = 8'b0;
        if (create_handle && !handle_created_once) begin
            my_handle = new(10);
            handle_created_once = 1'b1;
        end
        if (handle_created_once && my_handle != null) begin
            fork
                automatic MyDataClass fork_local_handle;
                fork_local_handle = new(20);
                my_handle.set_val(my_handle.val + 5);
                fork_local_handle.val = fork_local_handle.val * 2;
            join_none
            class_data_out = my_handle.val;
        end
    end
endmodule
module Module_ClassMemberAccess (
    input bit clk,
    input logic [7:0] in_member_val,
    output logic [7:0] out_member_res
);
    class MyMemberClass;
        logic [7:0] member_var;
        function new();
            member_var = 0;
        endfunction
    endclass
    MyMemberClass module_class_inst;
    logic initialised_inst = 1'b0;
    always @(posedge clk) begin : member_access_block
        out_member_res = 0;
        if (!initialised_inst) begin
            module_class_inst = new();
            initialised_inst = 1'b1;
        end
        if (module_class_inst != null) begin
            fork
                automatic int fork_local_temp = in_member_val + 1;
                module_class_inst.member_var = fork_local_temp;
                out_member_res = module_class_inst.member_var;
                dummy_member_task(module_class_inst.member_var);
                module_class_inst.member_var = module_class_inst.member_var + 5;
            join_none
            out_member_res = out_member_res + module_class_inst.member_var;
        end
    end
    task automatic dummy_member_task;
        input int val;
    endtask
endmodule
module Module_StaticVarInFork (
    input bit clk,
    input logic in_static_val,
    output logic out_static_res
);
    always @(posedge clk) begin : static_block
        static logic static_flag = 1'b0;
        if (in_static_val) begin
            fork
                if (static_flag == 1'b0) begin
                    static_flag = 1'b1;
                end
                out_static_res = static_flag;
            join_none
        end else begin
            out_static_res = static_flag;
        end
    end
endmodule
module Module_TaskDynScopeAndBinding (
    input bit clk,
    input logic [7:0] in_task_val,
    output logic [7:0] out_task_res
);
    logic [7:0] module_level_var;
    always @(posedge clk) begin
        module_level_var = in_task_val;
        out_task_res = 0;
        call_task_with_async_fork(module_level_var, out_task_res);
    end
    task automatic call_task_with_async_fork;
        input int param_in;
        output int param_out;
        automatic int task_local_var = 5;
        automatic event task_event;
        fork
            task_local_var = param_in + 1;
            param_out = task_local_var * 2;
            -> task_event;
        join_none
        param_out = param_out + task_local_var;
    endtask
endmodule
