module table_large_comb (
    input  logic  [7:0] in_bus,
    output logic  [3:0] out_a,
    output logic  [3:0] out_b,
    output logic  [3:0] out_c
);
    always_comb begin
        unique case (in_bus)
            8'd0  : begin out_a = 4'd0;  out_b = 4'd1;  out_c = 4'd2;  end
            8'd1  : begin out_a = 4'd1;  out_b = 4'd2;  out_c = 4'd3;  end
            8'd2  : begin out_a = 4'd2;  out_b = 4'd3;  out_c = 4'd4;  end
            8'd3  : begin out_a = 4'd3;  out_b = 4'd4;  out_c = 4'd5;  end
            8'd4  : begin out_a = 4'd4;  out_b = 4'd5;  out_c = 4'd6;  end
            8'd5  : begin out_a = 4'd5;  out_b = 4'd6;  out_c = 4'd7;  end
            8'd6  : begin out_a = 4'd6;  out_b = 4'd7;  out_c = 4'd8;  end
            8'd7  : begin out_a = 4'd7;  out_b = 4'd8;  out_c = 4'd9;  end
            8'd8  : begin out_a = 4'd8;  out_b = 4'd9;  out_c = 4'd10; end
            8'd9  : begin out_a = 4'd9;  out_b = 4'd10; out_c = 4'd11; end
            8'd10 : begin out_a = 4'd10; out_b = 4'd11; out_c = 4'd12; end
            8'd11 : begin out_a = 4'd11; out_b = 4'd12; out_c = 4'd13; end
            8'd12 : begin out_a = 4'd12; out_b = 4'd13; out_c = 4'd14; end
            8'd13 : begin out_a = 4'd13; out_b = 4'd14; out_c = 4'd15; end
            8'd14 : begin out_a = 4'd14; out_b = 4'd15; out_c = 4'd0;  end
            8'd15 : begin out_a = 4'd15; out_b = 4'd0;  out_c = 4'd1;  end
            8'd16 : begin out_a = 4'd0;  out_b = 4'd1;  out_c = 4'd2;  end
            8'd17 : begin out_a = 4'd1;  out_b = 4'd2;  out_c = 4'd3;  end
            8'd18 : begin out_a = 4'd2;  out_b = 4'd3;  out_c = 4'd4;  end
            8'd19 : begin out_a = 4'd3;  out_b = 4'd4;  out_c = 4'd5;  end
            8'd20 : begin out_a = 4'd4;  out_b = 4'd5;  out_c = 4'd6;  end
            8'd21 : begin out_a = 4'd5;  out_b = 4'd6;  out_c = 4'd7;  end
            8'd22 : begin out_a = 4'd6;  out_b = 4'd7;  out_c = 4'd8;  end
            8'd23 : begin out_a = 4'd7;  out_b = 4'd8;  out_c = 4'd9;  end
            8'd24 : begin out_a = 4'd8;  out_b = 4'd9;  out_c = 4'd10; end
            8'd25 : begin out_a = 4'd9;  out_b = 4'd10; out_c = 4'd11; end
            8'd26 : begin out_a = 4'd10; out_b = 4'd11; out_c = 4'd12; end
            8'd27 : begin out_a = 4'd11; out_b = 4'd12; out_c = 4'd13; end
            8'd28 : begin out_a = 4'd12; out_b = 4'd13; out_c = 4'd14; end
            8'd29 : begin out_a = 4'd13; out_b = 4'd14; out_c = 4'd15; end
            8'd30 : begin out_a = 4'd14; out_b = 4'd15; out_c = 4'd0;  end
            8'd31 : begin out_a = 4'd15; out_b = 4'd0;  out_c = 4'd1;  end
            8'd32 : begin out_a = 4'd0;  out_b = 4'd1;  out_c = 4'd2;  end
            8'd33 : begin out_a = 4'd1;  out_b = 4'd2;  out_c = 4'd3;  end
            8'd34 : begin out_a = 4'd2;  out_b = 4'd1;  out_c = 4'd0;  end
            default: begin out_a = 4'd0;  out_b = 4'd0;  out_c = 4'd0;  end
        endcase
    end
endmodule
module table_large_seq (
    input  logic        clk,
    input  logic [7:0]  data_in,
    output logic [7:0]  data_out1,
    output logic [7:0]  data_out2
);
    always_ff @(posedge clk) begin
        unique case (data_in)
            8'd0  : begin data_out1 <= 8'h00; data_out2 <= 8'h10; end
            8'd1  : begin data_out1 <= 8'h11; data_out2 <= 8'h21; end
            8'd2  : begin data_out1 <= 8'h22; data_out2 <= 8'h32; end
            8'd3  : begin data_out1 <= 8'h33; data_out2 <= 8'h43; end
            8'd4  : begin data_out1 <= 8'h44; data_out2 <= 8'h54; end
            8'd5  : begin data_out1 <= 8'h55; data_out2 <= 8'h65; end
            8'd6  : begin data_out1 <= 8'h66; data_out2 <= 8'h76; end
            8'd7  : begin data_out1 <= 8'h77; data_out2 <= 8'h87; end
            8'd8  : begin data_out1 <= 8'h88; data_out2 <= 8'h98; end
            8'd9  : begin data_out1 <= 8'h99; data_out2 <= 8'hA9; end
            8'd10 : begin data_out1 <= 8'hAA; data_out2 <= 8'hBA; end
            8'd11 : begin data_out1 <= 8'hBB; data_out2 <= 8'hCB; end
            8'd12 : begin data_out1 <= 8'hCC; data_out2 <= 8'hDC; end
            8'd13 : begin data_out1 <= 8'hDD; data_out2 <= 8'hED; end
            8'd14 : begin data_out1 <= 8'hEE; data_out2 <= 8'hFE; end
            8'd15 : begin data_out1 <= 8'hFF; data_out2 <= 8'h0F; end
            8'd16 : begin data_out1 <= 8'h10; data_out2 <= 8'h20; end
            8'd17 : begin data_out1 <= 8'h21; data_out2 <= 8'h31; end
            8'd18 : begin data_out1 <= 8'h32; data_out2 <= 8'h42; end
            8'd19 : begin data_out1 <= 8'h43; data_out2 <= 8'h53; end
            8'd20 : begin data_out1 <= 8'h54; data_out2 <= 8'h64; end
            8'd21 : begin data_out1 <= 8'h65; data_out2 <= 8'h75; end
            8'd22 : begin data_out1 <= 8'h76; data_out2 <= 8'h86; end
            8'd23 : begin data_out1 <= 8'h87; data_out2 <= 8'h97; end
            8'd24 : begin data_out1 <= 8'h98; data_out2 <= 8'hA8; end
            8'd25 : begin data_out1 <= 8'hA9; data_out2 <= 8'hB9; end
            8'd26 : begin data_out1 <= 8'hBA; data_out2 <= 8'hCA; end
            8'd27 : begin data_out1 <= 8'hCB; data_out2 <= 8'hDB; end
            8'd28 : begin data_out1 <= 8'hDC; data_out2 <= 8'hEC; end
            8'd29 : begin data_out1 <= 8'hED; data_out2 <= 8'hFD; end
            8'd30 : begin data_out1 <= 8'hFE; data_out2 <= 8'h0E; end
            8'd31 : begin data_out1 <= 8'h0F; data_out2 <= 8'h1F; end
            8'd32 : begin data_out1 <= 8'h20; data_out2 <= 8'h30; end
            8'd33 : begin data_out1 <= 8'h31; data_out2 <= 8'h41; end
            8'd34 : begin data_out1 <= 8'h42; data_out2 <= 8'h52; end
            8'd35 : begin data_out1 <= 8'h53; data_out2 <= 8'h63; end
            8'd36 : begin data_out1 <= 8'h64; data_out2 <= 8'h74; end
            8'd37 : begin data_out1 <= 8'h75; data_out2 <= 8'h85; end
            8'd38 : begin data_out1 <= 8'h86; data_out2 <= 8'h96; end
            8'd39 : begin data_out1 <= 8'h97; data_out2 <= 8'hA7; end
            default: begin data_out1 <= data_out1; data_out2 <= data_out2; end
        endcase
    end
endmodule
module table_partial (
    input  logic sel,
    output logic out_x,
    output logic out_y
);
    always_comb begin
        out_x = 1'b0;
        out_y = 1'b0;
        if (sel) begin
            out_x = 1'b1;
        end else begin
            out_y = 1'b1;
        end
    end
endmodule
module table_array_concat (
    input  logic [3:0] in0,
    input  logic [3:0] in1,
    input  logic [3:0] in2,
    output logic [11:0] result
);
    always_comb begin
        result = {in2, in1, in0};
    end
endmodule
