module Assertions_and_Cover_Properties (
    input clk,
    input reset_n,
    input logic [7:0] data_in,
    input logic val_in,
    output logic out_assertion,
    output logic out_cover
);
    logic [7:0] internal_reg_ff;
    logic delayed_val_ff;
    logic internal_cond;
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            internal_reg_ff <= 8'd0;
            delayed_val_ff <= 1'b0;
        end else begin
            internal_reg_ff <= data_in;
            delayed_val_ff <= val_in;
            assert(val_in) else $error("Immediate assert failed: val_in is false.");
            out_assertion = val_in;
            if (data_in == 8'hFF && val_in) begin
                assert(1'b0) else $error("Immediate assert failed: Data is FF and Valid.");
                out_assertion = 1'b0;
            end else begin
                out_assertion = 1'b1;
            end
        end
    end
    ap_data_stable: assert property (@(posedge clk) disable iff (!reset_n) (data_in == internal_reg_ff) |=> (data_in == internal_reg_ff))
    else begin
        out_assertion = 1'b0;
    end;
    cp_data_increase: cover property (@(posedge clk) disable iff (!reset_n) (data_in > internal_reg_ff));
    assign out_cover = 1'b1;
    always_comb begin
        internal_cond = (data_in > 8'd10);
        if (internal_cond && data_in[0] == 1'b1) begin
            assert (1'b1) else $error("Another immediate assert failure example.");
        end
        assert (data_in[7] == 1'b0) else $error("Immediate assert for data_in MSB failed.");
    end
endmodule
module Case_Assertions_Module (
    input logic [1:0] selector,
    input logic [3:0] value_a,
    input logic [3:0] value_b,
    output logic [7:0] case_result
);
    logic [7:0] temp_result_fp;
    logic [7:0] temp_result_cp;
    logic [7:0] temp_result_caz;
    logic [7:0] temp_result_ci;
    always_comb begin
        unique case (selector)
            2'b00: temp_result_fp = value_a + value_b;
            2'b01: temp_result_fp = value_a - value_b;
            2'b10: temp_result_fp = value_a * value_b;
            2'b11: temp_result_fp = value_a / value_b;
        endcase
        priority casex (value_a)
            4'b1x0x: temp_result_cp = 8'h10;
            4'b0x1x: temp_result_cp = 8'h20;
            default: temp_result_cp = 8'h00;
        endcase
        unique casez (value_b)
            4'b1???: temp_result_caz = 8'h30;
            4'b01??: temp_result_caz = 8'h40;
            4'b001?: temp_result_caz = 8'h50;
            default: temp_result_caz = 8'h00;
        endcase
        unique0 case ({value_a, value_b}) inside
            [10:15]: temp_result_ci = 8'h60;
            [20:25]: temp_result_ci = 8'h70;
            [30:35]: temp_result_ci = 8'h80;
            default: temp_result_ci = 8'h00;
        endcase
        case_result = temp_result_fp + temp_result_cp + temp_result_caz + temp_result_ci;
    end
endmodule
module Conditional_Assertions_Module (
    input logic in_a,
    input logic in_b,
    input logic in_c,
    output logic [1:0] if_out
);
    always_comb begin
        unique if (in_a && in_b) begin
            if_out = 2'b01;
        end else if (in_a && !in_b) begin
            if_out = 2'b10;
        end else begin
            if_out = 2'b00;
        end
        unique0 if (in_b && in_c) begin
            if_out = if_out | 2'b01;
        end else if (!in_b && in_c) begin
            if_out = if_out | 2'b10;
        end
    end
endmodule
module Past_and_Sampled_Module (
    input clk,
    input reset_n,
    input logic [7:0] data_in_sampled,
    input logic [7:0] data_in_past,
    output logic [7:0] sampled_out,
    output logic [7:0] past_out
);
    logic [7:0] internal_reg_sampled;
    logic [7:0] internal_reg_past;
    logic [7:0] past_val_1tick;
    logic [7:0] past_val_2ticks;
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            internal_reg_sampled <= 8'h00;
            internal_reg_past <= 8'h00;
        end else begin
            internal_reg_sampled <= data_in_sampled;
            internal_reg_past <= data_in_past;
        end
    end
    always_ff @(posedge clk) begin
        past_val_1tick <= $past(internal_reg_past);
        past_val_2ticks <= $past(data_in_past, 2);
    end
    assign past_out = past_val_1tick + past_val_2ticks;
    always_comb begin
        sampled_out = $sampled(internal_reg_sampled);
    end
endmodule
module Display_Tasks_Module (
    input clk,
    input reset_n,
    input logic event_trigger,
    input logic [3:0] monitor_val,
    input logic [3:0] strobe_val,
    output logic dummy_out
);
    logic monitor_state;
    logic strobe_pending_sig;
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            monitor_state <= 1'b1;
            strobe_pending_sig <= 1'b0;
        end else begin
            monitor_state <= ~monitor_state;
            strobe_pending_sig <= event_trigger;
        end
    end
    always_comb begin
        dummy_out = monitor_val + strobe_val;
        if (event_trigger) begin
            $info("Info message for event_trigger.");
            $warning("Warning message: Trigger active.");
            $error("Error message: Trigger is ON!");
            if (event_trigger && monitor_val == 4'hF) begin
                $fatal(1, "Fatal error: Monitor value reached max!");
            end
        end
        $monitor("Monitor: monitor_val = %0d, strobe_val = %0d", monitor_val, strobe_val);
        if (!monitor_state) begin
            $monitoroff;
        end
        if (strobe_pending_sig) begin
            $strobe("Strobe: Values at end of current delta cycle: %0d, %0d", monitor_val, strobe_val);
        end
    end
endmodule
module Assert_Control_and_Restrict_Module (
    input logic ctrl_on_i,
    input logic ctrl_off_i,
    input logic [7:0] data_val_i,
    output logic ctl_out_o
);
    always_comb begin
        if (ctrl_on_i) begin
            $assert_control (all, on);
        end
        if (ctrl_off_i) begin
            $assert_control (all, off);
        end
        ctl_out_o = data_val_i[0];
    end
    restrict property (data_val_i > 8'd100);
endmodule
