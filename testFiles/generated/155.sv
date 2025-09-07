module snippet (
    input wire clk,
    input int inj_i_val_1755007804947_722,
    input wire reset,
    output int inj_o_val_1755007804947_866
);
    // BEGIN: mod_automatic_task_ts1755007804948
    task automatic update_val(input int in_v, output int out_v);
        out_v = in_v * 2;
    endtask
    always_comb begin
        int temp_val_ts1755007804947;
        update_val(inj_i_val_1755007804947_722, temp_val_ts1755007804947);
        inj_o_val_1755007804947_866 = temp_val_ts1755007804947;
    end
    // END: mod_automatic_task_ts1755007804948
endmodule

