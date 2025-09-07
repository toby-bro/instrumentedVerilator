module assert_immediate_and_display (
    input logic i_cond,
    input logic [7:0] i_data,
    output logic o_status
);
    always_comb begin : assert_display_logic
        o_status = 1'b1;
        if (i_cond) begin : conditional_block_asserts
            assert (i_data != 8'hFF) else $error("Immediate assert failed: data is FF. Input: %h", i_data);
            void'($warning("Module: %m - Warning: i_data is %h when i_cond is true.", i_data));
            void'($info("Module: %m - Info: Processing conditional block. i_data=%h", i_data));
            if (i_data == 8'h00) begin
                void'($fatal(1, "Module: %m - Fatal: i_data is 00, simulation cannot continue."));
            end
        end else begin : else_block_asserts
            assert (i_data != 8'hEE) else $error("Immediate assert failed: data is EE when i_cond is false. Input: %h", i_data);
        end
    end
endmodule
module concurrent_assertions_and_past (
    input logic i_clk,
    input logic i_rst_n,
    input logic i_prop_en,
    input logic [3:0] i_data_in,
    output logic [3:0] o_past_data
);
    logic [3:0] q_data_delayed;
    always_ff @(posedge i_clk or negedge i_rst_n) begin : data_flop
        if (!i_rst_n) begin
            q_data_delayed <= 4'h0;
        end else begin
            q_data_delayed <= i_data_in;
        end
    end
    assign o_past_data = $past(i_data_in, 1, 4'h0, @(posedge i_clk));
    property p_data_stable_on_enable;
        @(posedge i_clk) disable iff (!i_rst_n)
        i_prop_en |-> ($stable(i_data_in));
    endproperty
    assert property (p_data_stable_on_enable) else $error("Data changed unexpectedly!");
    property p_input_range;
        @(posedge i_clk) i_data_in <= 4'd10;
    endproperty
    assume property (p_input_range);
    property p_data_toggle;
        @(posedge i_clk) (i_data_in == 4'hA) ##1 (i_data_in == 4'h5);
    endproperty
    cover property (p_data_toggle);
    property p_restrict_never_max_val;
        @(posedge i_clk) !(i_data_in == 4'hF);
    endproperty
    restrict property (p_restrict_never_max_val);
endmodule
module if_unique_priority_checks (
    input logic i_select_a,
    input logic i_select_b,
    input logic [2:0] i_val,
    output logic [3:0] o_result_if
);
    logic [3:0] o_result_unique_if;
    logic [3:0] o_result_unique0_if;
    always_comb begin : unique_if_block
        unique if (i_select_a && i_select_b) begin
            o_result_unique_if = i_val + 4'd1;
        end else if (i_select_a) begin
            o_result_unique_if = i_val + 4'd2;
        end else if (i_select_b) begin
            o_result_unique_if = i_val + 4'd3;
        end else begin
            o_result_unique_if = 4'hF;
        end
    end
    always_comb begin : unique0_if_block
        unique0 if (i_val == 3'd0) begin
            o_result_unique0_if = 4'd10;
        end else if (i_val == 3'd1) begin
            o_result_unique0_if = 4'd11;
        end else if (i_val == 3'd2) begin
            o_result_unique0_if = 4'd12;
        end
    end
    assign o_result_if = o_result_unique_if + o_result_unique0_if;
endmodule
module case_parallel_full_checks (
    input logic [2:0] i_opcode,
    input logic [7:0] i_operand_a,
    input logic [7:0] i_operand_b,
    output logic [15:0] o_calc_result
);
    logic [15:0] result_internal;
    logic [3:0] casex_res;
    logic [3:0] casez_res;
    logic range_match;
    always_comb begin : case_logic
        result_internal = 16'h0000;
        (* full_case *) priority case (i_opcode)
            3'd0: result_internal = i_operand_a + i_operand_b;
            3'd1: result_internal = i_operand_a - i_operand_b;
            3'd2: result_internal = i_operand_a * i_operand_b;
            3'd3: result_internal = {8'h00, i_operand_a} / {8'h00, i_operand_b};
            3'd4: result_internal = i_operand_a | i_operand_b;
            3'd5: result_internal = i_operand_a & i_operand_b;
            default: result_internal = 16'hAAAA;
        endcase
        (* parallel_case *) unique case (i_opcode)
            3'd0: result_internal = result_internal + 1;
            3'd6: result_internal = result_internal + 2;
            3'd7: result_internal = result_internal + 3;
        endcase
        unique0 casex (i_operand_a[3:0])
            4'b1???: casex_res = 4'h1;
            4'b01??: casex_res = 4'h2;
            4'b001?: casex_res = 4'h3;
            4'b0001: casex_res = 4'h4;
        endcase
        result_internal = result_internal + casex_res;
        unique0 casez (i_operand_b[3:0])
            4'b1zz?: casez_res = 4'h1;
            4'b01zz: casez_res = 4'h2;
            4'b001z: casez_res = 4'h3;
            4'b0001: casez_res = 4'h4;
        endcase
        result_internal = result_internal + casez_res;
        case (i_operand_a) inside
            [8'h10:8'h20], 8'hAA, 8'hBB: range_match = 1'b1;
            default: range_match = 1'b0;
        endcase
        result_internal = result_internal + {15'b0, range_match};
    end
    assign o_calc_result = result_internal;
endmodule
module monitor_strobe_and_sampled (
    input logic i_clk,
    input logic [7:0] i_data_val,
    output logic o_monitor_status
);
    logic [7:0] internal_reg_for_sampled;
    logic internal_toggle_for_monitor;
    logic temp_o_monitor_status;
    logic [7:0] sampled_output;
    always_ff @(posedge i_clk) begin : clocked_logic
        internal_reg_for_sampled <= i_data_val + 1;
        internal_toggle_for_monitor <= ~internal_toggle_for_monitor;
    end
    always_comb begin : monitor_activation_logic
        temp_o_monitor_status = 1'b1;
        if (i_data_val == 8'hAA) begin
            void'($monitor("Monitor event: Time %0t, data_val=%h, sampled_reg=%h, toggle=%b",
                     $time, i_data_val, internal_reg_for_sampled, internal_toggle_for_monitor));
            temp_o_monitor_status = 1'b1;
        end else if (i_data_val == 8'hBB) begin
            void'($monitoroff);
            temp_o_monitor_status = 1'b0;
        end else begin
            temp_o_monitor_status = 1'b1;
        end
        if (i_data_val == 8'hCC) begin
            void'($strobe("Strobe event: Current data_val=%h, internal_reg=%h",
                    i_data_val, internal_reg_for_sampled));
        end
        sampled_output = $sampled(internal_reg_for_sampled);
        o_monitor_status = temp_o_monitor_status ^ sampled_output[0];
    end
endmodule
module assert_control_statements (
    input logic [2:0] i_control_cmd,
    input logic i_flag_for_assert,
    output logic o_control_status
);
    always_comb begin : control_command_logic
        o_control_status = 1'b0;
        case (i_control_cmd)
            3'd0: begin
                (* ivl_assert_on *) ;
                o_control_status = 1'b1;
            end
            3'd1: begin
                (* ivl_assert_off(8'hC0, 8'h38) *) ;
                o_control_status = 1'b0;
            end
            3'd2: begin
                (* ivl_assert_kill *) ;
                o_control_status = 1'b0;
            end
            3'd3: begin
                (* ivl_assert_lock(8'h20, 8'h08) *) ;
                o_control_status = 1'b0;
            end
            3'd4: begin
                (* ivl_assert_pass_on(8'h10, 8'h38) *) ;
                o_control_status = 1'b0;
            end
            3'd5: begin
                (* ivl_assert_fail_on(8'h20, 8'h38) *) ;
                o_control_status = 1'b0;
            end
            default: begin
            end
        endcase
        if (i_flag_for_assert) begin
            assert (i_control_cmd != 3'd7) else $error("Control command 7 detected when flag is high.");
        end
    end
endmodule
