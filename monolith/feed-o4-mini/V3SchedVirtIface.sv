interface Ifc;
    logic a;
    logic b;
    modport mp_out (output a, b);
endinterface
module m1(input Ifc.mp_out vif, input logic in1, output logic out1);
    always @* begin
        vif.a = in1;
        out1 = vif.a;
    end
endmodule
module m2(input Ifc.mp_out vif, input logic clk, input logic in2, output logic out2);
    always @(posedge clk) begin
        vif.a <= in2;
        out2 <= vif.a;
    end
endmodule
module m3(input Ifc.mp_out vif, input logic cond3, input logic in3, output logic out3);
    always @* begin
        if (cond3) begin
            vif.a = in3;
            out3 = vif.b;
        end else begin
            vif.b = in3;
            out3 = vif.a;
        end
    end
endmodule
module m4(input Ifc.mp_out vif, input logic cond4, input logic in4, output logic out4);
    always @* begin
        if ((vif.a = in4)) begin
            out4 = vif.b;
        end
    end
endmodule
module m5(input Ifc.mp_out vif, input logic in5, output logic out5);
    logic temp5;
    always @* begin
        temp5 = 1'b0;
        while (in5) begin : while_loop
            vif.b = temp5;
            temp5 = vif.a;
            disable while_loop;
        end
        out5 = temp5;
    end
endmodule
module m6(input Ifc.mp_out vif, input logic in6, output logic out6);
    always @* begin
        vif.a = in6;
        out6 = vif.b;
    end
endmodule
module m7(input Ifc.mp_out vif, input logic in7a, input logic in7b, output logic out7);
    always @* begin
        vif.b = in7b;
    end
    always @* begin
        vif.a = in7a;
        vif.b = in7b;
        out7 = vif.a & vif.b;
    end
endmodule
module m8(input Ifc.mp_out vif, input logic [1:0] sel8, input logic in8, output logic out8);
    genvar i;
    generate
        for (i = 0; i < 2; i = i + 1) begin : genblk
            always @* begin
                if (sel8 == i)
                    vif.a = in8;
                else
                    vif.a = vif.a;
            end
        end
    endgenerate
    always @* begin
        out8 = vif.b;
    end
endmodule
module m9(input Ifc.mp_out vif, input logic [1:0] sel9, input logic in9, output logic out9);
    always @* begin
        case (sel9)
            2'd0: vif.a = in9;
            2'd1: vif.b = in9;
            default: begin end
        endcase
    end
    always @* begin
        out9 = vif.a;
    end
endmodule
module m10(input Ifc.mp_out vif, input logic in10, output logic out10);
    always @* begin
        begin : blk
            vif.a = in10;
            out10 = vif.b;
        end
    end
endmodule
module m11(input Ifc.mp_out vif, input logic in11, output logic out11);
    always @* begin
        fork : fork_block
            vif.b = in11;
        join_none
        disable fork_block;
        out11 = vif.a;
    end
endmodule
module m12(input Ifc.mp_out vif, input logic clk12, input logic in12, output logic out12);
    always @(posedge clk12) begin : proc_block
        vif.b <= in12;
        out12 <= vif.a;
    end
endmodule
module m13(input Ifc.mp_out vif, input logic in13, output logic out13);
    logic tmp13;
    always @* begin
        tmp13 = in13;
        vif.b = tmp13;
        out13 = tmp13;
    end
endmodule
module m14(input Ifc.mp_out vif, input logic in14, output logic out14);
    function logic f14(input logic x);
        f14 = x & vif.a;
    endfunction
    always @* begin
        out14 = f14(in14);
    end
endmodule
module m15(input Ifc.mp_out vif, input logic in15, output logic out15);
    task t15(input logic x);
        vif.b = x;
    endtask
    always @* begin
        t15(in15);
        out15 = vif.a;
    end
endmodule
