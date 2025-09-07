interface my_if;
    logic [7:0] data;
    logic ready;
    logic valid;
    modport FullAccess (input data, output ready, output valid);
    modport AccessIn (output data, output valid, input ready);
    modport AccessOut (input data, input valid, output ready);
endinterface
module StructExample (
    input logic [15:0] in_data,
    output logic [7:0] out_field_a,
    output logic [7:0] out_field_b
);
    typedef struct packed {
        logic [7:0] field_a;
        logic [7:0] field_b;
    } example_struct_t;
    example_struct_t my_struct;
    always_comb begin
        my_struct     = in_data;
        out_field_a   = my_struct.field_a;
        out_field_b   = my_struct.field_b;
    end
endmodule

module module_to_bind (
    input logic i_bind_clk,
    input logic [3:0] i_bind_control,
    output logic o_bind_status
);
    always_comb o_bind_status = |i_bind_control;
endmodule

module sequential_register_en (
    input logic clk,
    input logic [7:0] data_in,
    input logic en,
    output logic [7:0] data_out
);
    always_ff @(posedge clk) begin
        if (en) begin
            data_out <= data_in;
        end
    end
endmodule

module target_module_for_bind (
    input logic i_target_clk,
    input logic [7:0] i_target_data,
    output logic [7:0] o_target_result
);
    always_comb o_target_result = i_target_data + 1;
endmodule

module snippet #(
    parameter int WIDTH = 8
) (
    input wire clk,
    input bit [7:0] inj_data_in_1755007857171_540,
    input logic [31:0] inj_data_in_w_1755007857169_209,
    input logic inj_en_1755007857172_469,
    input logic [3:0] inj_i_control_1755007857168_230,
    input logic [7:0] inj_i_data_1755007857168_53,
    input wire [7:0] inj_i_in_1755007857168_918,
    input logic [7:0] inj_in3_f_1755007857169_853,
    input logic [15:0] inj_in_data_1755007857169_310,
    input bit inj_select_signal_1755007857171_802,
    input wire reset,
    output bit [7:0] inj_data_out_1755007857171_677,
    output logic [7:0] inj_data_out_1755007857172_684,
    output logic [31:0] inj_data_out_w_1755007857169_505,
    output logic [7:0] inj_o_out_1755007857168_221,
    output logic [7:0] inj_o_result_1755007857168_511,
    output logic inj_o_status_1755007857168_688,
    output logic [7:0] inj_out1_f_1755007857169_525,
    output logic [7:0] inj_out2_f_1755007857169_970,
    output logic [7:0] inj_out3_f_1755007857169_685,
    output logic [7:0] inj_out_field_a_1755007857169_1,
    output logic [7:0] inj_out_field_b_1755007857169_629,
    output logic inj_write_status_1755007857170_891
);
    // BEGIN: bind_directive_top_ts1755007857168
    // BEGIN: mod_module_attrs_ts1755007857169
    logic [WIDTH-1:0] r_data_ts1755007857168;
        // BEGIN: SimpleLogicTest_ts1755007857171
        logic [7:0] temp_data_ts1755007857171;
            sequential_register_en sequential_register_en_inst_1755007857172_9533 (
                .data_in(inj_i_data_1755007857168_53),
                .en(inj_en_1755007857172_469),
                .data_out(inj_data_out_1755007857172_684),
                .clk(clk)
            );
        always_comb begin
            if (inj_select_signal_1755007857171_802) begin
                temp_data_ts1755007857171 = inj_data_in_1755007857171_540 + 1;
            end else begin
                temp_data_ts1755007857171 = inj_data_in_1755007857171_540 - 1;
            end
            inj_data_out_1755007857171_677 = temp_data_ts1755007857171;
        end
        // END: SimpleLogicTest_ts1755007857171

        // BEGIN: module_sequential_writes_ts1755007857170
        my_if vif_bus();
        always_comb begin
            vif_bus.data = inj_i_data_1755007857168_53;
            vif_bus.ready = 1'b1;
            vif_bus.valid = 1'b0;
            inj_write_status_1755007857170_891 = vif_bus.ready;
        end
        // END: module_sequential_writes_ts1755007857170

        // BEGIN: split_independent_nb_ts1755007857170
        always @(posedge clk) begin
            inj_out1_f_1755007857169_525 <= inj_i_data_1755007857168_53;
            inj_out2_f_1755007857169_970 <= r_data_ts1755007857168;
            inj_out3_f_1755007857169_685 <= inj_in3_f_1755007857169_853;
        end
        // END: split_independent_nb_ts1755007857170

        StructExample StructExample_inst_1755007857169_8095 (
            .in_data(inj_in_data_1755007857169_310),
            .out_field_a(inj_out_field_a_1755007857169_1),
            .out_field_b(inj_out_field_b_1755007857169_629)
        );
        // BEGIN: ModWideBus_ts1755007857169
        assign inj_data_out_w_1755007857169_505 = ~inj_data_in_w_1755007857169_209;
        // END: ModWideBus_ts1755007857169

    always_comb begin
        r_data_ts1755007857168 = inj_i_in_1755007857168_918;
    end
    assign inj_o_out_1755007857168_221 = r_data_ts1755007857168;
    // END: mod_module_attrs_ts1755007857169

    target_module_for_bind target_inst(
        .i_target_clk   (clk),
        .i_target_data  (inj_i_data_1755007857168_53),
        .o_target_result(inj_o_result_1755007857168_511)
    );
    module_to_bind bind_inst(
        .i_bind_clk     (clk),
        .i_bind_control (inj_i_control_1755007857168_230),
        .o_bind_status  (inj_o_status_1755007857168_688)
    );
    // END: bind_directive_top_ts1755007857168
endmodule

