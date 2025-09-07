module ModAssertDisplay (
    input logic clk,
    input logic rst_n,
    input logic [7:0] data_in,
    output logic [7:0] data_out
);
    logic trigger_assert_pass;
    logic trigger_assert_fail;
    logic trigger_assume_pass;
    logic trigger_assume_fail;
    logic trigger_cover;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            data_out <= 8'd0;
            trigger_assert_pass <= 1'b0;
            trigger_assert_fail <= 1'b0;
            trigger_assume_pass <= 1'b0;
            trigger_assume_fail <= 1'b0;
            trigger_cover <= 1'b0;
        end else begin
            data_out <= data_in + 1;
            if (data_in == 8'd1) $info("INFO: Data is %0d", data_in);
            if (data_in == 8'd2) $warning("WARNING: Data is %0d", data_in);
            if (data_in == 8'd3) $error("ERROR: Data is %0d", data_in);
            if (data_in == 8'd4) $fatal(0, "FATAL: Data is %0d, terminating.", data_in);
            trigger_assert_pass <= (data_in == 8'd5);
            trigger_assert_fail <= (data_in == 8'd6);
            trigger_assume_pass <= (data_in == 8'd7);
            trigger_assume_fail <= (data_in == 8'd8); 
            trigger_cover <= (data_in == 8'd9);
        end
    end
    always_comb begin
        if (trigger_assert_pass) begin
            assert ((data_in == 8'd5)) else $error("Immediate assert pass condition failed.");
        end
        if (trigger_assert_fail) begin
            assert ((data_in != 8'd6)) else $error("Immediate assert fail condition should have failed.");
        end
    end
    always_comb begin
        if (trigger_assume_pass) begin
            assume ((data_in == 8'd7));
        end
        if (trigger_assume_fail) begin
            assume ((data_in == 8'd10)); 
        end
    end
    always_comb begin
        if (trigger_cover) begin
            cover ((data_in == 8'd9));
        end
    end
endmodule
module ModMonitorStrobe (
    input logic clk,
    input logic rst_n,
    input logic [3:0] counter_val,
    output logic [3:0] monitor_out
);
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            monitor_out <= 4'd0;
        end else begin
            monitor_out <= counter_val;
            if (counter_val == 4'd1) begin
                $monitor("MONITOR: Counter is %0d, Monitor Out is %0d", counter_val, monitor_out);
            end
            if (counter_val == 4'd2) begin
                $strobe("STROBE: Counter is %0d, Monitor Out is %0d", counter_val, monitor_out);
            end
            if (counter_val == 4'd3) begin
                $monitoroff;
            end
        end
    end
endmodule
module ModCaseIfAsserts (
    input logic [1:0] sel_if,
    input logic [2:0] sel_case,
    input logic [3:0] data_x_z,
    output logic result_if,
    output logic [1:0] result_case
);
    always_comb begin : UniqueIfBlock
        result_if = 1'b0;
        unique if (sel_if == 2'b00) begin
            result_if = 1'b1;
        end else if (sel_if == 2'b01) begin
            result_if = 1'b0;
        end else begin
            result_if = 1'b1; 
        end
    end
    always_comb begin : Unique0IfBlock
        unique0 if (sel_if == 2'b00) begin
            result_if = 1'b0;
        end else if (sel_if == 2'b01) begin
            result_if = 1'b1;
        end
    end
    always_comb begin : CaseBlock
        result_case = 2'b00;
        priority case (sel_case)
            3'b000: result_case = 2'b01;
            3'b001: result_case = 2'b10;
            3'b010: result_case = 2'b11;
            default: result_case = 2'b00;
        endcase
        unique case (sel_case)
            3'b000: result_case = 2'b01;
            3'b001: result_case = 2'b10;
        endcase
        unique0 case (sel_case)
            3'b000: result_case = 2'b01;
            3'b001: result_case = 2'b10;
        endcase
        full case (sel_case)
            3'b100: result_case = 2'b01;
            3'b101: result_case = 2'b10;
        endcase
        parallel case (sel_case)
            3'b000: result_case = 2'b01;
            3'b000: result_case = 2'b10;
            3'b001: result_case = 2'b11;
        endcase
        casex (data_x_z)
            4'b101x: result_case = 2'b01;
            4'b101z: result_case = 2'b10;
            4'b00??: result_case = 2'b11;
            default: result_case = 2'b00;
        endcase
        casez (data_x_z)
            4'b101z: result_case = 2'b01;
            4'b00??: result_case = 2'b10;
            default: result_case = 2'b11;
        endcase
        case (data_x_z) inside
            [4'd5:4'd7]: result_case = 2'b01;
            {4'd9, 4'd11}: result_case = 2'b10;
            default: result_case = 2'b00;
        endcase
    end
endmodule
module ModSampledPast (
    input logic clk,
    input logic rst_n,
    input logic [7:0] data_in,
    output logic [7:0] past_data_out,
    output logic sampled_val_out
);
    logic [7:0] internal_reg;
    logic internal_var_to_write;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            internal_reg <= 8'd0;
            internal_var_to_write <= 1'b0;
        end else begin
            internal_reg <= data_in;
            past_data_out <= $past(internal_reg);
            logic [7:0] past2_val;
            past2_val = $past(data_in, 2);
            if (data_in == 8'd10) begin
                internal_var_to_write <= 1'b1;
            end else begin
                internal_var_to_write <= 1'b0;
            end
        end
    end
    always_comb begin
        sampled_val_out = $sampled(internal_var_to_write);
    end
    logic past_const_val;
    always_comb begin
        past_const_val = $past(1'b1);
    end
endmodule
module ModAssertCtl (
    input logic clk,
    input logic rst_n,
    input logic [1:0] control_type_select,
    output logic dummy_out
);
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            dummy_out <= 1'b0;
        end else begin
            dummy_out <= control_type_select[0];
            if (control_type_select == 2'b00) begin
                $assertcontrol(on, assert);
                $assertcontrol(on, unique, cover);
                $assertcontrol(on, assume, expect);
                $assertcontrol(on);
            end else if (control_type_select == 2'b01) begin
                $assertcontrol(off, assert, cover);
                $assertcontrol(off);
            end else if (control_type_select == 2'b10) begin
                $assertcontrol(kill, unique0, assert);
                $assertcontrol(kill);
            end else begin
                $assertcontrol(on, expect);
                $assertcontrol(on, priority);
                $assertcontrol(pass_on);
            end
        end
    end
endmodule
module ModConcurrentAssert (
    input logic clk,
    input logic rst_n,
    input logic enable_in,
    input logic request_in,
    output logic grant_out
);
    logic state_q;
    logic [1:0] counter_q;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state_q <= 1'b0;
            counter_q <= 2'b00;
            grant_out <= 1'b0;
        end else begin
            state_q <= enable_in ? ~state_q : state_q;
            counter_q <= enable_in ? counter_q + 1 : counter_q;
            grant_out <= request_in && enable_in;
        end
    end
    property p_request_grant;
        @(posedge clk) request_in |-> ##1 grant_out;
    endproperty
    A_request_grant: assert property (p_request_grant) else $error("Request without grant");
    property p_counter_roll_over;
        @(posedge clk) (counter_q == 2'b11) |-> (counter_q == 2'b00);
    endproperty
    C_counter_roll_over: cover property (p_counter_roll_over);
    always @(posedge clk) begin : proc_assert_block
        property p_always_proc_assert;
            @(posedge clk) (counter_q == 2'b10) |-> (counter_q == 2'b11);
        endproperty
        A_always_proc_assert: assert property (p_always_proc_assert);
    end
    property p_state_toggle;
        @(negedge clk) $rose(state_q) or $fell(state_q);
    endproperty
    A_state_toggle: assert property (p_state_toggle) else $warning("State did not toggle.");
endmodule
module ModRestrict (
    input logic clk,
    input logic reset,
    output logic dummy_out
);
    logic [7:0] count;
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            count <= 8'd0;
            dummy_out <= 1'b0;
        end else begin
            count <= count + 1;
            dummy_out <= count[0];
            if (count == 8'd5) begin
                $restrict(count < 8'd10);
            end
        end
    end
endmodule
