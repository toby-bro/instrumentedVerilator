module table_int_case (
    input  logic [3:0] in1,          
    input  logic [2:0] in2,          
    output logic [7:0] out1,
    output logic [7:0] out2
);
    always @* begin
        out1 = 8'h00;
        unique case ({in2, in1})
            7'd0  : begin out1 = 8'h01;  out2 = 8'hFE; end
            7'd1  : begin out1 = 8'h02;                end
            7'd2  : begin out1 = 8'h03;  out2 = 8'hFC; end
            7'd3  : begin out1 = 8'h04;                end
            7'd4  : begin out1 = 8'h05;  out2 = 8'hFA; end
            7'd5  : begin out1 = 8'h06;                end
            7'd6  : begin out1 = 8'h07;  out2 = 8'hF8; end
            7'd7  : begin out1 = 8'h08;                end
            7'd8  : begin out1 = 8'h09;  out2 = 8'hF6; end
            7'd9  : begin out1 = 8'h0A;                end
            7'd10 : begin out1 = 8'h0B; out2 = 8'hF4; end
            7'd11 : begin out1 = 8'h0C;               end
            7'd12 : begin out1 = 8'h0D; out2 = 8'hF2; end
            7'd13 : begin out1 = 8'h0E;               end
            7'd14 : begin out1 = 8'h0F; out2 = 8'hF0; end
            7'd15 : begin out1 = 8'h10;               end
            7'd16 : begin out1 = 8'h11; out2 = 8'hEE; end
            7'd17 : begin out1 = 8'h12;               end
            7'd18 : begin out1 = 8'h13; out2 = 8'hEC; end
            7'd19 : begin out1 = 8'h14;               end
            7'd20 : begin out1 = 8'h15; out2 = 8'hEA; end
            7'd21 : begin out1 = 8'h16;               end
            7'd22 : begin out1 = 8'h17; out2 = 8'hE8; end
            7'd23 : begin out1 = 8'h18;               end
            7'd24 : begin out1 = 8'h19; out2 = 8'hE6; end
            7'd25 : begin out1 = 8'h1A;               end
            7'd26 : begin out1 = 8'h1B; out2 = 8'hE4; end
            7'd27 : begin out1 = 8'h1C;               end
            7'd28 : begin out1 = 8'h1D; out2 = 8'hE2; end
            7'd29 : begin out1 = 8'h1E;               end
            7'd30 : begin out1 = 8'h1F; out2 = 8'hE0; end
            7'd31 : begin out1 = 8'h20;               end
            7'd32 : begin out1 = 8'h21; out2 = 8'hDE; end
            7'd33 : begin out1 = 8'h22;               end
            7'd34 : begin out1 = 8'h23; out2 = 8'hDC; end
            7'd35 : begin out1 = 8'h24;               end
            7'd36 : begin out1 = 8'h25; out2 = 8'hDA; end
            7'd37 : begin out1 = 8'h26;               end
            7'd38 : begin out1 = 8'h27; out2 = 8'hD8; end
            7'd39 : begin out1 = 8'h28;               end
            default: out1 = 8'hFF;  
        endcase
    end
endmodule
module table_case_str (
    input  logic [4:0] sel,   
    output string      msg
);
    always @* begin
        case (sel)
            5'd0  : msg = "ZERO";
            5'd1  : msg = "ONE";
            5'd2  : msg = "TWO";
            5'd3  : msg = "THREE";
            5'd4  : msg = "FOUR";
            5'd5  : msg = "FIVE";
            5'd6  : msg = "SIX";
            5'd7  : msg = "SEVEN";
            5'd8  : msg = "EIGHT";
            5'd9  : msg = "NINE";
            5'd10 : msg = "TEN";
            5'd11 : msg = "ELEVEN";
            5'd12 : msg = "TWELVE";
            5'd13 : msg = "THIRTEEN";
            5'd14 : msg = "FOURTEEN";
            5'd15 : msg = "FIFTEEN";
            5'd16 : msg = "SIXTEEN";
            5'd17 : msg = "SEVENTEEN";
            5'd18 : msg = "EIGHTEEN";
            5'd19 : msg = "NINETEEN";
            5'd20 : msg = "TWENTY";
            5'd21 : msg = "TWENTY-ONE";
            5'd22 : msg = "TWENTY-TWO";
            5'd23 : msg = "TWENTY-THREE";
            5'd24 : msg = "TWENTY-FOUR";
            5'd25 : msg = "TWENTY-FIVE";
            5'd26 : msg = "TWENTY-SIX";
            5'd27 : msg = "TWENTY-SEVEN";
            5'd28 : msg = "TWENTY-EIGHT";
            5'd29 : msg = "TWENTY-NINE";
            5'd30 : msg = "THIRTY";
            5'd31 : msg = "THIRTY-ONE";
            default: msg = "";
        endcase
    end
endmodule
module table_case_real (
    input  logic [5:0] addr,  
    output real        value
);
    always @* begin
        case (addr)
            6'd0  : value = 0.0;
            6'd1  : value = 0.5;
            6'd2  : value = 1.0;
            6'd3  : value = 1.5;
            6'd4  : value = 2.0;
            6'd5  : value = 2.5;
            6'd6  : value = 3.0;
            6'd7  : value = 3.5;
            6'd8  : value = 4.0;
            6'd9  : value = 4.5;
            6'd10 : value = 5.0;
            6'd11 : value = 5.5;
            6'd12 : value = 6.0;
            6'd13 : value = 6.5;
            6'd14 : value = 7.0;
            6'd15 : value = 7.5;
            6'd16 : value = 8.0;
            6'd17 : value = 8.5;
            6'd18 : value = 9.0;
            6'd19 : value = 9.5;
            6'd20 : value = 10.0;
            6'd21 : value = 10.5;
            6'd22 : value = 11.0;
            6'd23 : value = 11.5;
            6'd24 : value = 12.0;
            6'd25 : value = 12.5;
            6'd26 : value = 13.0;
            6'd27 : value = 13.5;
            6'd28 : value = 14.0;
            6'd29 : value = 14.5;
            6'd30 : value = 15.0;
            6'd31 : value = 15.5;
            6'd32 : value = 16.0;
            6'd33 : value = 16.5;
            default: value = 99.99;
        endcase
    end
endmodule
