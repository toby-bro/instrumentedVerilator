module bits_query_mod #(parameter WIDTH = 16) (
    input  logic [WIDTH-1:0] in_data,
    output logic [31:0]      out_bits
);
    localparam int BITS_OF_INT = $bits(int);
    always_comb begin
        out_bits = $bits(in_data);
    end
endmodule
module typename_query_mod (
    input  logic  in_sel,
    output string out_type
);
    logic [7:0] vector_example;
    always_comb begin
        if (in_sel)
            vector_example = 8'hAA;
        else
            vector_example = 8'h55;
        out_type = $typename(vector_example);
    end
endmodule
module isunbounded_query_mod (
    input  logic dummy_in,
    output logic is_unb
);
    parameter P1 = 12;
    always_comb begin
        is_unb = $isunbounded(P1);
    end
endmodule
module low_query_mod (
    input  logic trigger,
    output logic [31:0] low_val
);
    logic [7:0] arr [0:3];
    always_comb begin
        arr[0] = trigger ? 8'h1 : 8'h0;
        arr[1] = 8'h2;
        arr[2] = 8'h3;
        arr[3] = 8'h4;
        low_val = $low(arr);
    end
endmodule
module high_query_mod (
    input  logic trigger,
    output logic [31:0] high_val
);
    logic [7:0] arr [0:5];
    always_comb begin
        arr[0] = 8'hA ^ {7'h0,trigger};
        arr[1] = 8'hB;
        arr[2] = 8'hC;
        arr[3] = 8'hD;
        arr[4] = 8'hE;
        arr[5] = 8'hF;
        high_val = $high(arr);
    end
endmodule
module left_query_mod (
    input  logic trig,
    output logic [31:0] left_val
);
    logic [7:0] packed_left [3:0];
    always_comb begin
        packed_left[0] = 8'h11 ^ {7'h0,trig};
        packed_left[1] = 8'h22;
        packed_left[2] = 8'h33;
        packed_left[3] = 8'h44;
        left_val = $left(packed_left);
    end
endmodule
module right_query_mod (
    input  logic trig,
    output logic [31:0] right_val
);
    logic [0:3][7:0] reversed_arr;
    always_comb begin
        reversed_arr[0] = 8'hAA & {7'h7F,trig};
        reversed_arr[1] = 8'hBB;
        reversed_arr[2] = 8'hCC;
        reversed_arr[3] = 8'hDD;
        right_val = $right(reversed_arr);
    end
endmodule
module size_query_mod (
    input  logic dummy,
    output logic [31:0] size_val
);
    logic [3:0] matrix [0:2][0:4];
    always_comb begin
        matrix[0][0] = dummy;
        size_val = $size(matrix);
    end
endmodule
module increment_query_mod (
    input  logic dummy,
    output logic [31:0] inc_val
);
    logic [7:0] asc_arr [3:0];
    logic [7:0] desc_arr [3:0];
    logic [0:3][7:0] asc_dir_arr;
    logic [3:0][7:0] desc_dir_arr;
    always_comb begin
        asc_arr  = '{8'h0,8'h1,8'h2,8'h3};
        desc_arr = '{8'hF,8'hE,8'hD,8'hC};
        inc_val = $increment(asc_arr);
    end
endmodule
module dimensions_query_mod (
    input  logic trig,
    output logic [31:0] dim_val
);
    logic [15:0] big_array [0:1][0:3];
    always_comb begin
        big_array[0][0] = trig ? 16'h1234 : 16'h4321;
        dim_val = $dimensions(big_array);
    end
endmodule
module unpacked_dimensions_query_mod (
    input  logic trig,
    output logic [31:0] undim_val
);
    logic [31:0] sample_array [0:2][0:7];
    always_comb begin
        sample_array[0][0] = trig ? 32'hDEADBEEF : 32'hCAFEBABE;
        undim_val = $unpacked_dimensions(sample_array);
    end
endmodule
