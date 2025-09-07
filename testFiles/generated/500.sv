module mod_unused_ports (
    input wire unused_in,
    output logic unused_out
);
    assign unused_out = unused_in;
endmodule

module snippet (
    input wire clk,
    input logic inj_c1_x_1755007921302_56,
    input logic inj_c2_x_1755007921302_127,
    input logic inj_c3_x_1755007921302_356,
    input bit inj_cfg_in_1755007921302_961,
    input logic [7:0] inj_v1_x_1755007921302_403,
    input logic [7:0] inj_v2_x_1755007921302_165,
    input logic [7:0] inj_v3_x_1755007921302_976,
    input logic [7:0] inj_v4_x_1755007921302_164,
    input wire reset,
    output bit inj_cfg_out_1755007921302_777,
    output logic [7:0] inj_out_x_1755007921302_17,
    output logic inj_unused_out_1755007921302_206,
    output logic inj_unused_out_1755007921302_469
);
    // BEGIN: mod_unused_ports_ts1755007921302
    // BEGIN: Module_ConfigKeywords_ts1755007921302
    // BEGIN: split_ifelse_chain_ts1755007921302
    always @(posedge clk) begin
        if (inj_c1_x_1755007921302_56) begin
            inj_out_x_1755007921302_17 <= inj_v1_x_1755007921302_403;
        end else if (inj_c2_x_1755007921302_127) begin
            inj_out_x_1755007921302_17 <= inj_v2_x_1755007921302_165;
        end else if (inj_c3_x_1755007921302_356) begin
            inj_out_x_1755007921302_17 <= inj_v3_x_1755007921302_976;
        end else begin
            inj_out_x_1755007921302_17 <= inj_v4_x_1755007921302_164;
        end
    end
    // END: split_ifelse_chain_ts1755007921302

    assign inj_cfg_out_1755007921302_777 = inj_cfg_in_1755007921302_961;
    // END: Module_ConfigKeywords_ts1755007921302

    mod_unused_ports mod_unused_ports_inst_1755007921302_1892 (
        .unused_out(inj_unused_out_1755007921302_469),
        .unused_in(reset)
    );
    assign inj_unused_out_1755007921302_206 = clk;
    // END: mod_unused_ports_ts1755007921302
endmodule

