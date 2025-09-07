class vl_process_base;
  typedef enum { FINISHED, RUNNING, SUSPENDED } state_e;
  state_e proc_state;
  function new();
    proc_state = RUNNING;
  endfunction
  function void state(state_e new_state);
    proc_state = new_state;
  endfunction
endclass
class vl_timing_scheduler_base;
  function void resume(); endfunction
  function void commit(); endfunction
  function void doPostUpdates(); endfunction
  function bit isDelayScheduler(); return 0; endfunction
  function bit isTriggerScheduler(); return 0; endfunction
  function bit isDynamicTriggerScheduler(); return 0; endfunction
endclass
class vl_delay_scheduler extends vl_timing_scheduler_base;
  function new(); endfunction
  function bit isDelayScheduler(); return 1; endfunction
endclass
class vl_trigger_scheduler extends vl_timing_scheduler_base;
  function new(); endfunction
  function bit isTriggerScheduler(); return 1; endfunction
endclass
class vl_dynamic_trigger_scheduler extends vl_timing_scheduler_base;
  function new(); endfunction
  function bit isDynamicTriggerScheduler(); return 1; endfunction
endclass
class VlSymsp;
endclass
module mod_TimingTriggers (
    input logic clk_i,
    input logic rst_ni,
    input bit   trigger_cond_i,
    input bit   delay_cond_i,
    output logic [7:0] data_o
);
  logic [7:0] reg_a, reg_b;
  logic event_a, event_b;
  vl_delay_scheduler   delay_sched_inst;
  vl_trigger_scheduler trig_sched_inst;
  vl_process_base      process_inst;
  always_comb begin
    delay_sched_inst = new();
    trig_sched_inst = new();
    process_inst = new();
  end
  always_ff @(posedge clk_i or negedge rst_ni) begin : ff_block_a
    if (!rst_ni) begin
      reg_a <= 8'h00;
    end else begin
      if (delay_cond_i) begin
        wait (reg_a == 8'hAA);
        delay_sched_inst.resume();
        reg_a <= 8'hAA;
      end else begin
        reg_a <= reg_a + 1;
      end
    end
  end
  always_ff @(posedge clk_i or negedge rst_ni) begin : latch_block_b
    if (!rst_ni) begin
      reg_b <= 8'h00;
      event_b <= 0;
    end else begin
      if (trigger_cond_i) begin
        event_b <= 1;
        wait ( !trigger_cond_i );
        trig_sched_inst.commit();
        reg_b <= reg_b + 1;
      end else begin
        event_b <= 0;
        reg_b <= 8'h00;
      end
    end
  end
  always_comb begin : remap_domains_logic
    if (event_a || event_b) begin
      data_o = reg_a + reg_b;
    end else begin
      data_o = 8'hFF;
    end
  end
  always_comb begin : comb_block_c
    event_a = (reg_a == 8'hF0);
    if (event_a) begin
      delay_sched_inst.resume();
    end
  end
endmodule
module mod_SuspendableProcess (
    input logic enable_i,
    input logic [3:0] in_data_i,
    output logic [3:0] out_data_o,
    output logic [3:0] status_o
);
  logic [3:0] internal_var_0;
  logic [3:0] internal_var_1;
  logic [3:0] shared_var;
  vl_process_base p_inst_h;
  always_comb begin
    p_inst_h = new();
  end
  always_ff @(posedge enable_i) begin : my_suspendable_proc
    internal_var_0 <= in_data_i + 1;
    status_o <= internal_var_0;
    fork : fork_in_proc
      begin : named_block_a
        wait (internal_var_0 == 4'd5);
        shared_var <= in_data_i * 2;
        p_inst_h.state(vl_process_base::SUSPENDED);
      end
      begin : named_block_b
        internal_var_1 <= in_data_i / 2;
        status_o <= internal_var_1;
      end
    join_any
  end
  assign out_data_o = shared_var;
endmodule
module mod_ComplexFork (
    input logic clk_i,
    input logic run_i,
    input logic [7:0] val_i,
    output logic [7:0] result_o,
    output logic done_o
);
  logic [7:0] data_val;
  logic [7:0] func_local_var;
  logic       fork_sync_flag;
  logic [7:0] temp_result_o;
  logic       temp_done_o;
  VlSymsp symsp_inst;
  always_comb begin
    symsp_inst = new();
  end
  function automatic logic [7:0] my_task_func(logic [7:0] arg_data, ref logic ref_flag, input VlSymsp symsp);
    logic [7:0] temp_local;
    temp_local = arg_data + ref_flag;
    ref_flag = !ref_flag;
    return temp_local * 2;
  endfunction
  always_ff @(posedge clk_i) begin : main_process
    if (!run_i) begin
      data_val <= 0;
      fork_sync_flag <= 0;
      func_local_var <= 0;
      temp_result_o <= 0;
      temp_done_o <= 0;
    end else begin
      data_val <= val_i;
      fork_sync_flag <= 1'b0;
      fork : outer_fork_join_none
        begin : block_a
          logic [7:0] block_a_local;
          block_a_local = data_val + 1;
          wait (data_val > 50);
          func_local_var <= my_task_func(block_a_local, fork_sync_flag, symsp_inst);
        end
        begin : block_b
          logic [7:0] block_b_local;
          block_b_local = data_val - 1;
          temp_done_o <= (block_b_local < 10);
        end
      join_none
      fork : middle_fork_join_any
        begin : block_c
          logic [7:0] temp_c;
          temp_c = func_local_var + 3;
          wait (fork_sync_flag);
          temp_result_o <= temp_c;
        end
        begin : block_d
          data_val <= data_val + 1;
        end
      join_any
      fork : inner_fork_join
        begin : block_e
          logic [7:0] temp_e;
          wait (temp_result_o > 100);
          temp_e = temp_result_o * 2;
          data_val <= temp_e;
        end
        begin : block_f
          temp_done_o <= !temp_done_o;
        end
      join
    end
  end
  assign result_o = temp_result_o;
  assign done_o = temp_done_o;
endmodule
module mod_DelayScheduler (
    input logic start_i,
    input logic trigger_i,
    output logic [1:0] state_o
);
  vl_dynamic_trigger_scheduler dyn_trig_sched;
  vl_process_base proc_a;
  always_comb begin
    dyn_trig_sched = new();
    proc_a = new();
  end
  always_ff @(posedge start_i) begin : delay_process
    state_o <= 2'b00;
    if (start_i) begin
      wait (1'b1);
      dyn_trig_sched.resume();
      state_o <= 2'b01;
      dyn_trig_sched.doPostUpdates();
      wait (trigger_i);
      dyn_trig_sched.resume();
      state_o <= 2'b10;
      proc_a.state(vl_process_base::FINISHED);
    end
  end
endmodule
module mod_TriggerAndDynamicScheduler (
    input logic enable_sig_i,
    input logic data_valid_i,
    input logic [7:0] input_data_i,
    output logic [7:0] processed_data_o
);
  logic [7:0] current_data;
  logic       data_stable;
  vl_trigger_scheduler trig_sch;
  vl_dynamic_trigger_scheduler dyn_trig_sch;
  vl_process_base proc_b;
  always_comb begin
    trig_sch = new();
    dyn_trig_sch = new();
    proc_b = new();
  end
  always_ff @(posedge enable_sig_i) begin : scheduler_complex_proc
    current_data <= 8'h00;
    data_stable <= 1'b0;
    processed_data_o <= 8'h00; 
    if (enable_sig_i) begin
      wait (data_valid_i);
      trig_sch.resume();
      current_data <= input_data_i;
      data_stable <= 1'b1;
      wait (data_valid_i && current_data > 8'h50);
      dyn_trig_sch.resume();
      dyn_trig_sch.doPostUpdates();
      processed_data_o <= current_data + 1;
      proc_b.state(vl_process_base::SUSPENDED);
    end else begin
      processed_data_o <= 8'hXX; 
    end
  end
endmodule
