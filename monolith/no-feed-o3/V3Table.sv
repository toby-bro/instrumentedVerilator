module lookup_table_case_large (
    input  logic [7:0] addr,
    output logic [7:0] data
);
    always_comb begin
        case (addr)
            8'h00: data = 8'h01;
            8'h01: data = 8'h02;
            8'h02: data = 8'h03;
            8'h03: data = 8'h04;
            8'h04: data = 8'h05;
            8'h05: data = 8'h06;
            8'h06: data = 8'h07;
            8'h07: data = 8'h08;
            8'h08: data = 8'h09;
            8'h09: data = 8'h0A;
            8'h0A: data = 8'h0B;
            8'h0B: data = 8'h0C;
            8'h0C: data = 8'h0D;
            8'h0D: data = 8'h0E;
            8'h0E: data = 8'h0F;
            8'h0F: data = 8'h10;
            8'h10: data = 8'h11;
            8'h11: data = 8'h12;
            8'h12: data = 8'h13;
            8'h13: data = 8'h14;
            8'h14: data = 8'h15;
            8'h15: data = 8'h16;
            8'h16: data = 8'h17;
            8'h17: data = 8'h18;
            8'h18: data = 8'h19;
            8'h19: data = 8'h1A;
            8'h1A: data = 8'h1B;
            8'h1B: data = 8'h1C;
            8'h1C: data = 8'h1D;
            8'h1D: data = 8'h1E;
            8'h1E: data = 8'h1F;
            8'h1F: data = 8'h20;
            8'h20: data = 8'h21;
            8'h21: data = 8'h22;
            8'h22: data = 8'h23;
            8'h23: data = 8'h24;
            8'h24: data = 8'h25;
            8'h25: data = 8'h26;
            8'h26: data = 8'h27;
            8'h27: data = 8'h28;
            8'h28: data = 8'h29;
            8'h29: data = 8'h2A;
            8'h2A: data = 8'h2B;
            8'h2B: data = 8'h2C;
            8'h2C: data = 8'h2D;
            8'h2D: data = 8'h2E;
            8'h2E: data = 8'h2F;
            8'h2F: data = 8'h30;
            8'h30: data = 8'h31;
            8'h31: data = 8'h32;
            8'h32: data = 8'h33;
            8'h33: data = 8'h34;
            8'h34: data = 8'h35;
            8'h35: data = 8'h36;
            8'h36: data = 8'h37;
            8'h37: data = 8'h38;
            8'h38: data = 8'h39;
            8'h39: data = 8'h3A;
            8'h3A: data = 8'h3B;
            8'h3B: data = 8'h3C;
            8'h3C: data = 8'h3D;
            8'h3D: data = 8'h3E;
            8'h3E: data = 8'h3F;
            8'h3F: data = 8'h40;
            default: data = 8'h00;
        endcase
    end
endmodule
module large_if_nonblocking (
    input  logic        clk,
    input  logic [4:0]  a,
    input  logic [4:0]  b,
    output logic [4:0]  y0,
    output logic [4:0]  y1
);
    always_ff @(posedge clk) begin
        if      (a == 5'd0 ) begin y0 <= 5'd0 ; y1 <= b      ; end
        else if (a == 5'd1 ) begin y0 <= 5'd1 ; y1 <= b + 1  ; end
        else if (a == 5'd2 ) begin y0 <= 5'd2 ; y1 <= b + 2  ; end
        else if (a == 5'd3 ) begin y0 <= 5'd3 ; y1 <= b + 3  ; end
        else if (a == 5'd4 ) begin y0 <= 5'd4 ; y1 <= b + 4  ; end
        else if (a == 5'd5 ) begin y0 <= 5'd5 ; y1 <= b + 5  ; end
        else if (a == 5'd6 ) begin y0 <= 5'd6 ; y1 <= b + 6  ; end
        else if (a == 5'd7 ) begin y0 <= 5'd7 ; y1 <= b + 7  ; end
        else if (a == 5'd8 ) begin y0 <= 5'd8 ; y1 <= b + 8  ; end
        else if (a == 5'd9 ) begin y0 <= 5'd9 ; y1 <= b + 9  ; end
        else if (a == 5'd10) begin y0 <= 5'd10; y1 <= b + 10 ; end
        else if (a == 5'd11) begin y0 <= 5'd11; y1 <= b + 11 ; end
        else if (a == 5'd12) begin y0 <= 5'd12; y1 <= b + 12 ; end
        else if (a == 5'd13) begin y0 <= 5'd13; y1 <= b + 13 ; end
        else if (a == 5'd14) begin y0 <= 5'd14; y1 <= b + 14 ; end
        else if (a == 5'd15) begin y0 <= 5'd15; y1 <= b + 15 ; end
        else if (a == 5'd16) begin y0 <= 5'd16; y1 <= b + 16 ; end
        else if (a == 5'd17) begin y0 <= 5'd17; y1 <= b + 17 ; end
        else if (a == 5'd18) begin y0 <= 5'd18; y1 <= b + 18 ; end
        else if (a == 5'd19) begin y0 <= 5'd19; y1 <= b + 19 ; end
        else if (a == 5'd20) begin y0 <= 5'd20; y1 <= b + 20 ; end
        else if (a == 5'd21) begin y0 <= 5'd21; y1 <= b + 21 ; end
        else if (a == 5'd22) begin y0 <= 5'd22; y1 <= b + 22 ; end
        else if (a == 5'd23) begin y0 <= 5'd23; y1 <= b + 23 ; end
        else if (a == 5'd24) begin y0 <= 5'd24; y1 <= b + 24 ; end
        else if (a == 5'd25) begin y0 <= 5'd25; y1 <= b + 25 ; end
        else if (a == 5'd26) begin y0 <= 5'd26; y1 <= b + 26 ; end
        else if (a == 5'd27) begin y0 <= 5'd27; y1 <= b + 27 ; end
        else if (a == 5'd28) begin y0 <= 5'd28; y1 <= b + 28 ; end
        else if (a == 5'd29) begin y0 <= 5'd29; y1 <= b + 29 ; end
        else if (a == 5'd30) begin y0 <= 5'd30; y1 <= b + 30 ; end
        else if (a == 5'd31) begin y0 <= 5'd31; y1 <= b + 31 ; end
        else begin
            y0 <= 5'd31;
            y1 <= 5'd31;
        end
    end
endmodule
module coverage_example (
    input  logic [3:0] state,
    output logic       flag
);
    always_comb begin
        flag = 1'b0;
        if (state == 4'd0) flag = 1'b1;
        else if (state == 4'd1) flag = 1'b1;
        else if (state == 4'd2) flag = 1'b1;
        else if (state == 4'd3) flag = 1'b1;
        cover (state == 4'd2);
        cover (state == 4'd3);
    end
endmodule
module impure_function_example (
    input  logic [7:0] data_in,
    output logic [7:0] data_out
);
    always_comb begin
        automatic int unsigned temp_rand;
        temp_rand = $urandom_range(255);
        data_out  = data_in ^ temp_rand[7:0];
    end
endmodule
module partial_assign_example (
    input  logic       sel,
    input  logic [7:0] din0,
    input  logic [7:0] din1,
    output logic [7:0] dout
);
    always_comb begin
        if (sel) begin
            dout = din0;
        end
    end
endmodule
