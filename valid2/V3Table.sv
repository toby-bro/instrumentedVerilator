module combin_table (
    input  logic [2:0] sel,
    input  logic       inb,
    output logic [7:0] out
);
    logic [7:0] tmp;
    always_comb begin
        out = 8'h00;
        if (sel == 3'd0)  out = 8'h01;
        if (sel == 3'd1)  out = 8'h02;
        if (sel == 3'd2)  out = 8'h03;
        if (sel == 3'd3)  out = 8'h04;
        if (sel == 3'd4)  out = 8'h05;
        if (sel == 3'd5)  out = 8'h06;
        if (sel == 3'd6)  out = 8'h07;
        if (sel == 3'd7)  out = 8'h08;
        if (inb) begin
            if (sel[0]) out = out ^ 8'h10;
            if (sel[1]) out = out ^ 8'h20;
            if (sel[2]) out = out ^ 8'h40;
        end
        tmp = sel + inb;
        tmp = tmp + 8'h1;
        tmp = tmp ^ out;
        if (&sel)  out = out + 8'h33;
        if (|sel)  out = out - 8'h11;
        if (sel == 3'd0)       out = out + 8'h01;
        else if (sel == 3'd1)  out = out + 8'h02;
        else if (sel == 3'd2)  out = out + 8'h03;
        else if (sel == 3'd3)  out = out + 8'h04;
    end
endmodule
module multi_out (
    input  logic [3:0] a,
    input  logic [3:0] b,
    output logic       y0,
    output logic       y1,
    output logic       y2,
    output logic       y3
);
    always_comb begin
        if (a[0]) begin
            y0 = a[0] ^ b[0];
        end
        if (a[1]) begin
            y1 = a[1] & b[1];
        end else if (b[1]) begin
            y1 = a[1] | b[1];
        end else begin
            y1 = 1'b0;
        end
        case (a[3:2])
            2'b00: begin
                y2 = a[2];
                y3 = b[2];
            end
            2'b01: begin
                y2 = a[3];
            end
            2'b10: begin
                y3 = b[3];
            end
            default: begin
                y2 = 1'b0;
                y3 = 1'b0;
            end
        endcase
    end
endmodule
module many_assigns (
    input  logic [15:0] inp,
    output wire  [15:0] out0,
    output wire  [15:0] out1,
    output wire  [15:0] out2,
    output wire  [15:0] out3
);
    assign out0 = inp;
    assign out1 = ~inp;
    assign out2 = {inp[7:0], inp[15:8]};
    assign out3 = inp ^ 16'h55AA;
endmodule
module array_concat (
    input  logic [1:0] idx,
    output logic [7:0] o
);
    logic [7:0] mem [0:3];
    always_comb begin
        o = {mem[idx][7:4], mem[idx][3:0]};
    end
endmodule
module real_process (
    input  real  rin,
    input  logic sel,
    output real  rout
);
    always_comb begin
        if (sel) begin
            rout = rin * 2.0;
        end else begin
        end
    end
endmodule
module case_table (
    input  logic [4:0] sel,
    output logic [7:0] o
);
    always_comb begin
        o = 8'h00;
        case (sel)
            5'd0  : o = 8'h01;
            5'd1  : o = 8'h02;
            5'd2  : o = 8'h03;
            5'd3  : o = 8'h04;
            5'd4  : o = 8'h05;
            5'd5  : o = 8'h06;
            5'd6  : o = 8'h07;
            5'd7  : o = 8'h08;
            5'd8  : o = 8'h09;
            5'd9  : o = 8'h0A;
            5'd10 : o = 8'h0B;
            5'd11 : o = 8'h0C;
            5'd12 : o = 8'h0D;
            5'd13 : o = 8'h0E;
            5'd14 : o = 8'h0F;
            5'd15 : o = 8'h10;
            5'd16 : o = 8'h11;
            5'd17 : o = 8'h12;
            5'd18 : o = 8'h13;
            5'd19 : o = 8'h14;
            5'd20 : o = 8'h15;
            5'd21 : o = 8'h16;
            5'd22 : o = 8'h17;
            5'd23 : o = 8'h18;
            5'd24 : o = 8'h19;
            5'd25 : o = 8'h1A;
            5'd26 : o = 8'h1B;
            5'd27 : o = 8'h1C;
            5'd28 : o = 8'h1D;
            5'd29 : o = 8'h1E;
            5'd30 : o = 8'h1F;
            5'd31 : o = 8'h20;
        endcase
    end
endmodule
