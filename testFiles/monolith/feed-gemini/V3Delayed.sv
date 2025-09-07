module ShadowVarScalar (
    input logic clk,
    input logic rst_n,
    input logic in_s,
    output logic out_s
);
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            out_s <= 1'b0;
        end else begin
            out_s <= in_s;
        end
    end
endmodule
module ShadowVarMaskedMixed (
    input logic clk,
    input logic rst_n,
    input logic [7:0] in_packed,
    output logic [7:0] out_packed
);
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            out_packed <= 8'b0;
        end else begin
            out_packed[7:3] <= in_packed[7:3];
            out_packed[4:0] = in_packed[4:0];
        end
    end
endmodule
module FlagSharedUnpacked (
    input logic clk,
    input logic rst_n,
    input logic [7:0] in_data,
    input logic [1:0] idx,
    output logic [7:0] out_unpacked [0:3]
);
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            for (int i=0; i<4; i++) begin
                out_unpacked[i] <= 8'b0;
            end
        end else begin
            out_unpacked[idx] <= in_data;
            if (idx < 3) begin
                out_unpacked[idx+1] <= in_data + 1;
            end
        end
    end
endmodule
module FlagUniqueSuspendable (
    input logic clk,
    input logic rst_n,
    input logic in_flag_unique,
    output logic out_flag_unique
);
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            out_flag_unique <= 1'b0;
        end else begin
            fork : my_fork_block
                out_flag_unique <= in_flag_unique;
            join_none
        end
    end
endmodule
module ValueQueueLoopArrays (
    input logic clk,
    input logic rst_n,
    input logic [7:0] in_loop_data,
    output logic [7:0] out_loop_arr [0:3]
);
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            for (int i=0; i<4; i++) begin
                out_loop_arr[i] <= 8'b0;
            end
        end else begin
            for (int i=0; i<4; i++) begin
                out_loop_arr[i] <= in_loop_data + i;
            end
        end
    end
endmodule
module ValueQueueLoopPartial (
    input logic clk,
    input logic rst_n,
    input logic [7:0] in_loop_partial_data,
    output logic [7:0] out_loop_partial_arr [0:3]
);
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            for (int i=0; i<4; i++) begin
                out_loop_partial_arr[i] <= 8'b0;
            end
        end else begin
            for (int i=0; i<4; i++) begin
                out_loop_partial_arr[i][3:0] <= in_loop_partial_data[3:0];
            end
        end
    end
endmodule
module NbaInSystemVerilogFunction (
    input logic clk,
    input logic rst_n,
    input logic in_func_nb,
    output logic out_func_nb
);
    function automatic logic get_nb_val(input logic val);
        return val;
    endfunction
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            out_func_nb <= 1'b0;
        end else begin
            out_func_nb <= get_nb_val(in_func_nb);
        end
    end
endmodule
module NbaInStaticTask (
    input logic clk,
    input logic rst_n,
    input logic in_static_task_nb,
    output logic out_static_task_nb
);
    logic internal_reg;
    task update_internal_nb_val(input logic val);
        internal_reg <= val;
    endtask
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            internal_reg <= 1'b0;
            out_static_task_nb <= 1'b0;
        end else begin
            update_internal_nb_val(in_static_task_nb);
            out_static_task_nb = internal_reg;
        end
    end
endmodule
module DelayedEventLogic (
    input logic clk,
    input logic rst_n,
    input logic trigger_event,
    output logic event_status
);
    event my_sig_event;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            event_status <= 1'b0;
        end else begin
            if (trigger_event) begin
                -> my_sig_event;
            end
            wait(my_sig_event);
            event_status <= 1'b1;
        end
    end
endmodule
