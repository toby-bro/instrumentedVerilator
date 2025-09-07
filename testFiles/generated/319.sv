interface my_if;
    logic [7:0] data;
    logic ready;
    logic valid;
    modport FullAccess (input data, output ready, output valid);
    modport AccessIn (output data, output valid, input ready);
    modport AccessOut (input data, input valid, output ready);
endinterface
module case_priority_casex_complex_mod (
    input logic [1:0] case_expr,
    input logic [3:0] case_inside_val,
    output logic [4:0] internal_out
);
    always @* begin
        priority casex ({case_expr, case_inside_val[1:0]})
            4'b1???: internal_out = 24;
            4'b?1??: internal_out = 25;  
            4'b??1?: internal_out = 26;  
            4'b???1: internal_out = 27;  
            4'b0000: internal_out = 28;  
            default: internal_out = 29;
        endcase
    end
endmodule

module snippet (
    input wire clk,
    input logic [3:0] inj_case_inside_val_1755007861642_249,
    input logic [7:0] inj_data_case_a_1755007861641_871,
    input logic [7:0] inj_data_case_b_1755007861641_104,
    input logic inj_data_in_1755007861643_913,
    input logic inj_enable_1755007861643_941,
    input wire [1:0] inj_i_sel_1755007861644_122,
    input wire [3:0] inj_i_val_1755007861644_761,
    input logic [1:0] inj_select_case_1755007861641_409,
    input wire reset,
    output logic inj_case_output_ready_1755007861641_874,
    output logic inj_data_out_1755007861643_572,
    output logic [4:0] inj_internal_out_1755007861642_173,
    output logic inj_o_done_1755007861644_859,
    output logic [3:0] inj_o_out_1755007861644_278
);
    // BEGIN: module_case_write_ts1755007861642
    // BEGIN: ModClockedConditional_ts1755007861643
    logic reg_data_ts1755007861643;
        // BEGIN: mod_basic_ts1755007861644
        logic r_state_ts1755007861644;
            // BEGIN: mod_case_block_attrs_ts1755007861645
            logic [3:0] l_temp_ts1755007861645;
            always_comb begin
                (* full_case *)
                (* parallel_case *)
                case (inj_i_sel_1755007861644_122)
                    2'b00: l_temp_ts1755007861645 = inj_i_val_1755007861644_761;
                    2'b01: l_temp_ts1755007861645 = inj_i_val_1755007861644_761 << 1;
                    2'b10: l_temp_ts1755007861645 = inj_i_val_1755007861644_761 >> 1;
                    default: l_temp_ts1755007861645 = 4'bxxxx;
                endcase
                (* coverage_off *)
                begin : my_named_block
                    inj_o_out_1755007861644_278 = l_temp_ts1755007861645;
                end
            end
            // END: mod_case_block_attrs_ts1755007861645

        parameter int PARAM_BASIC = 42;
        always_ff @(posedge clk) begin
            r_state_ts1755007861644 <= ~r_state_ts1755007861644;
        end
        always_comb begin
            inj_o_done_1755007861644_859 = r_state_ts1755007861644;
        end
        // END: mod_basic_ts1755007861644

    always @(posedge clk) begin
    if (inj_enable_1755007861643_941) begin
        reg_data_ts1755007861643 <= inj_data_in_1755007861643_913;
    end
    end
    assign inj_data_out_1755007861643_572 = reg_data_ts1755007861643;
    // END: ModClockedConditional_ts1755007861643

    case_priority_casex_complex_mod case_priority_casex_complex_mod_inst_1755007861642_824 (
        .internal_out(inj_internal_out_1755007861642_173),
        .case_expr(inj_select_case_1755007861641_409),
        .case_inside_val(inj_case_inside_val_1755007861642_249)
    );
    my_if case_vif_inst();
    always_comb begin
        case (inj_select_case_1755007861641_409)
            2'b00: begin
                case_vif_inst.data = 8'hAA;
                case_vif_inst.valid = 1'b1;
                case_vif_inst.ready = 1'b0;
            end
            2'b01: begin
                case_vif_inst.data = inj_data_case_a_1755007861641_871;
                case_vif_inst.valid = 1'b0;
                case_vif_inst.ready = 1'b1;
            end
            2'b10: begin
                case_vif_inst.data = inj_data_case_b_1755007861641_104;
                case_vif_inst.valid = 1'b1;
                case_vif_inst.ready = 1'b1;
            end
            default: begin
                case_vif_inst.data = 8'hFF;
                case_vif_inst.valid = 1'b0;
                case_vif_inst.ready = 1'b0;
            end
        endcase
        inj_case_output_ready_1755007861641_874 = case_vif_inst.ready;
    end
    // END: module_case_write_ts1755007861642
endmodule

