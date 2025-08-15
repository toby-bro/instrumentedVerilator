module ForceCombLogic (
    input logic [7:0] in_data,
    input logic       in_en_force,
    input logic       in_en_release,
    input logic [7:0] in_force_val,
    output logic [7:0] out_result
);
    logic [7:0] comb_var;
    logic       single_bit_var;
    logic [3:0] half_byte_var;
    always_comb begin
        if (in_data[0]) begin
            comb_var = in_data;
        end else begin
            comb_var = {8{1'b0}};
        end
        single_bit_var = comb_var[7];
        half_byte_var  = comb_var[3:0];
    end
    assign out_result = comb_var + 8'd1;
    always_latch begin
        if (in_en_force) begin
            force comb_var       = in_force_val;
            force single_bit_var = in_force_val[0];
            force half_byte_var  = in_force_val[3:0];
        end
    end
    always_latch begin
        if (in_en_release) begin
            release comb_var;
            release single_bit_var;
            release half_byte_var;
        end
    end
endmodule
module ForceSeqLogic (
    input logic clk,
    input logic rst_n,
    input logic [15:0] d_in,
    input logic        force_cond_a,
    input logic        force_cond_b,
    input logic        force_cond_c,
    input logic [15:0] force_val_a,
    input logic [15:0] force_val_b,
    output logic [15:0] q_out
);
    logic [15:0] seq_data_a_q;
    logic [15:0] seq_data_b_q;
    logic [15:0] seq_data_a_wire;
    logic [15:0] seq_data_b_wire;
    logic [15:0] intermediate_force_target;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            seq_data_a_q <= 16'h0000;
            seq_data_b_q <= 16'h0000;
        end else begin
            seq_data_a_q <= d_in;
            seq_data_b_q <= seq_data_a_q;
        end
    end
    assign seq_data_a_wire = seq_data_a_q;
    assign seq_data_b_wire = seq_data_b_q;
    assign q_out = seq_data_a_wire + seq_data_b_wire + intermediate_force_target;
    always_latch begin
        if (force_cond_a) begin
            force seq_data_a_wire = force_val_a;
        end else begin
            release seq_data_a_wire;
        end
    end
    always_latch begin
        if (force_cond_b) begin
            force seq_data_b_wire = force_val_b;
        end else begin
            release seq_data_b_wire;
        end
    end
    always_latch begin
        if (force_cond_c) begin
            force intermediate_force_target = seq_data_a_wire;
        end else begin
            release intermediate_force_target;
        end
    end
endmodule
module ForceWireTypes (
    input wire [3:0] in_wire_val,
    input logic      en_force_wire,
    input logic      en_release_wire,
    output wire [3:0] out_wire_val
);
    wire [3:0] my_net;
    assign my_net = in_wire_val;
    assign out_wire_val = my_net;
    always_latch begin
        if (en_force_wire) begin
            force my_net = 4'hF;
        end
        if (en_release_wire) begin
            release my_net;
        end
    end
endmodule
module ForceProcContexts (
    input logic [7:0] data_in,
    input logic       cmd_force,
    input logic       cmd_release,
    input logic       cmd_process,
    output logic [7:0] data_out
);
    logic [7:0] func_target_var;
    logic [7:0] task_target_var;
    function automatic logic [7:0] process_and_force(logic [7:0] val, logic do_force);
        logic [7:0] internal_func_var;
        internal_func_var = val + 1;
        if (do_force) begin
            force func_target_var = internal_func_var;
        end else begin
            release func_target_var;
        end
        return internal_func_var;
    endfunction
    task automatic process_and_release(logic [7:0] val, logic do_release);
        logic [7:0] internal_task_var;
        internal_task_var = val - 1;
        if (do_release) begin
            release task_target_var;
        end else begin
            force task_target_var = internal_task_var;
        end
    endtask
    always_comb begin
        func_target_var = 8'h00;
        task_target_var = 8'h00;
        if (cmd_process) begin
            data_out = process_and_force(data_in, cmd_force);
            process_and_release(data_in, cmd_release);
            data_out = data_out | func_target_var | task_target_var;
        end else begin
            data_out = 8'h00;
        end
    end
endmodule
module ForceComplexCond (
    input logic [3:0] in_val,
    input logic       en_f1,
    input logic       en_f2,
    input logic       en_r1,
    input logic       cond_expr,
    output logic [3:0] out_final_val
);
    wire [3:0] var_A;
    logic [3:0] var_B;
    assign var_A = in_val * 2;
    always_comb begin
        var_B = (var_A > 4'd5) ? (var_A + 4'd1) : (var_A - 4'd1);
    end
    always_latch begin
        if (en_f1) begin
            force var_A = 4'hA;
        end else if (en_r1) begin
            release var_A;
        end
    end
    always_latch begin
        if (en_f2 && cond_expr) begin
            force var_B = 4'hC;
        end else begin
            release var_B;
        end
    end
    assign out_final_val = var_A + var_B;
endmodule
