module always_comb_assign (
    input logic [15:0] in,
    output logic [15:0] out
);
    always_comb begin
        out = in;
    end
endmodule

module unsupported_logand_expr (
    input wire clk,
    input logic [7:0] in_a_m9,
    input logic [7:0] in_b_m9,
    input logic [15:0] inj_in_1755538576786_60,
    input logic [2:0] inj_sel_in_1755538576787_890,
    input wire rst,
    output reg [7:0] inj_data_out_1755538576787_912,
    output logic [15:0] inj_out_1755538576786_399,
    output logic out_m9
);
    logic [7:0] var_m9;
        // BEGIN: Module_ControlFlow_ts1755538576787
        reg [7:0] temp_ts1755538576787;
        always_comb begin
            unique case (inj_sel_in_1755538576787_890)
                3'b000: temp_ts1755538576787 = in_a_m9;
                3'b001: temp_ts1755538576787 = in_a_m9 + 1;
                3'b010: temp_ts1755538576787 = in_a_m9 - 1;
                default: temp_ts1755538576787 = 8'hAA;
            endcase
        end
        always_ff @(posedge clk or negedge rst) begin
            if (!rst)
                inj_data_out_1755538576787_912 <= 8'h00;
            else
                inj_data_out_1755538576787_912 <= temp_ts1755538576787;
        end
        // END: Module_ControlFlow_ts1755538576787

        always_comb_assign always_comb_assign_inst_1755538576786_1140 (
            .in(inj_in_1755538576786_60),
            .out(inj_out_1755538576786_399)
        );
    always_comb begin
        var_m9 = in_a_m9;
        if ((var_m9 > 10) && (in_b_m9 < 5)) begin
            out_m9 = 1;
        end else begin
            out_m9 = 0;
        end
        var_m9++;
    end
endmodule

