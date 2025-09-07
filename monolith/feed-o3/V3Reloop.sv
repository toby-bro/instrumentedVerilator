module reloop_neg_offset(
    input  logic [7:0] in_arr [0:15],
    output logic [7:0] out_arr [0:15]
);
    always_comb begin
        out_arr[0] = in_arr[1];
        out_arr[1] = in_arr[2];
        out_arr[2] = in_arr[3];
        out_arr[3] = in_arr[4];
        out_arr[4] = in_arr[5];
    end
endmodule
module reloop_pos_offset(
    input  logic [7:0] in_arr [0:15],
    output logic [7:0] out_arr [0:15]
);
    always_comb begin
        out_arr[2] = in_arr[0];
        out_arr[3] = in_arr[1];
        out_arr[4] = in_arr[2];
        out_arr[5] = in_arr[3];
        out_arr[6] = in_arr[4];
    end
endmodule
module reloop_const_rhs(
    input  logic dummy_in,
    output logic [7:0] out_arr [0:7]
);
    always_comb begin
        out_arr[0] = 8'hAA;
        out_arr[1] = 8'hAA;
        out_arr[2] = 8'hAA;
        out_arr[3] = 8'hAA;
        out_arr[4] = 8'hAA;
        out_arr[5] = 8'hAA;
    end
endmodule
module reloop_same_var(
    input  logic clk,
    output logic [7:0] out_sample
);
    logic [7:0] buffer [0:3];
    always_comb begin
        buffer[0] = buffer[1];
        buffer[1] = buffer[2];
        buffer[2] = buffer[3];
    end
    assign out_sample = buffer[0];
endmodule
module reloop_dynamic_idx(
    input  logic [3:0] idx,
    input  logic [7:0] in_arr [0:15],
    output logic [7:0] dout
);
    always_comb begin
        dout = in_arr[idx];
    end
endmodule
module reloop_bigwidth_idx(
    input  logic [7:0] din,
    output logic [7:0] dout
);
    logic [7:0] arr [0:0];
    always_comb begin
        arr[64'd0] = din;
        dout = arr[64'd0];
    end
endmodule
module reloop_zero_offset(
    input  logic [7:0] src [0:7],
    output logic [7:0] dst [0:7]
);
    always_comb begin
        dst[0] = src[0];
        dst[1] = src[1];
        dst[2] = src[2];
        dst[3] = src[3];
    end
endmodule
