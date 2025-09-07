module BitwiseAssign (
    input logic [3:0] in_a,
    input logic [3:0] in_b,
    output logic [3:0] out_y
);
    assign out_y = in_a ^ in_b;
endmodule

module ModRegister (
    input logic din,
    output logic dout
);
    always @* begin
        dout = din;
    end
endmodule

module split_ifelse_chain (
    input logic c1_x,
    input logic c2_x,
    input logic c3_x,
    input logic clk_x,
    input logic [3:0] inj_in_a_1755538610443_297,
    input logic [3:0] inj_in_b_1755538610443_599,
    input wire rst,
    input logic [7:0] v1_x,
    input logic [7:0] v2_x,
    input logic [7:0] v3_x,
    input logic [7:0] v4_x,
    output logic inj_dout_1755538610444_530,
    output logic [3:0] inj_out_y_1755538610443_84,
    output logic [7:0] out_x
);
    ModRegister ModRegister_inst_1755538610444_1534 (
        .din(c1_x),
        .dout(inj_dout_1755538610444_530)
    );
    BitwiseAssign BitwiseAssign_inst_1755538610443_5189 (
        .in_b(inj_in_b_1755538610443_599),
        .out_y(inj_out_y_1755538610443_84),
        .in_a(inj_in_a_1755538610443_297)
    );
    always @(posedge clk_x) begin
        if (c1_x) begin
            out_x <= v1_x;
        end else if (c2_x) begin
            out_x <= v2_x;
        end else if (c3_x) begin
            out_x <= v3_x;
        end else begin
            out_x <= v4_x;
        end
    end
endmodule

