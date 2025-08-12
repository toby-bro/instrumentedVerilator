module comb_mux(input logic [1:0] sel, input logic a, b, output logic y);
    always_comb begin
        case(sel)
            2'd0: y = 1'b0;
            2'd1: y = a;
            2'd2: y = b;
            default: y = 1'b1;
        endcase
    end
endmodule
module seq_ff(input logic clk, reset, d, output logic q);
    always_ff @(posedge clk or posedge reset) begin
        if (reset) q <= 1'b0;
        else q <= d;
    end
endmodule
module param_mod#(parameter int N = 8)(input logic [N-1:0] in, output logic [N-1:0] out);
    genvar i;
    generate
        for (i = 0; i < N; i = i + 1) begin : bit_rev
            assign out[i] = in[N-1-i];
        end
    endgenerate
endmodule
module function_mod(input logic [3:0] x, output logic [3:0] y);
    function logic [3:0] myfunc(input logic [3:0] v);
        begin
            myfunc = {v[0], v[1], v[2], v[3]};
        end
    endfunction
    always_comb begin
        y = myfunc(x);
    end
endmodule
module class_mod(input logic clk, reset, en, output logic [7:0] out);
    class myclass;
        rand logic [7:0] data;
        function void compute(input logic [7:0] in, output logic [7:0] o);
            o = in + 8'h1;
        endfunction
    endclass
    myclass obj;
    logic [7:0] data_reg;
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            data_reg <= '0;
            obj = new;
        end else if (en) begin
            obj.compute(data_reg, out);
            data_reg <= obj.data;
        end
    end
endmodule
module generate_mod(input logic [3:0] bus_in, output logic [3:0] bus_out);
    genvar j;
    generate
        for (j = 0; j < 4; j = j + 1) begin : gen_loop
            assign bus_out[j] = ~bus_in[j];
        end
    endgenerate
endmodule
module array_mod(input logic [3:0][7:0] arr_in, output logic [3:0][7:0] arr_out);
    integer m, n;
    always_comb begin
        for (m = 0; m < 4; m = m + 1) begin
            for (n = 0; n < 8; n = n + 1) begin
                arr_out[m][n] = arr_in[m][n];
            end
        end
    end
endmodule
module enum_mod(input logic [1:0] sel, output logic out_bit);
    typedef enum logic [1:0] {ID0 = 2'b00, ID1 = 2'b01, ID2 = 2'b10, ID3 = 2'b11} id_t;
    id_t id;
    always_comb begin
        id = id_t'(sel);
        unique case (id)
            ID0: out_bit = 1'b0;
            ID1: out_bit = 1'b1;
            ID2: out_bit = sel[0];
            default: out_bit = sel[1];
        endcase
    end
endmodule
module reduction_mod(input logic [7:0] in, output logic out_and, out_or, out_xor);
    assign out_and = &in;
    assign out_or  = |in;
    assign out_xor = ^in;
endmodule
