module bit_sel_basic(input logic [7:0] in, output logic out);
    assign out = in[3];
endmodule
module range_sel_basic(input logic [15:0] in, output logic [3:0] out);
    assign out = in[7:4];
endmodule
module sel_plus_minus_basic(input logic [15:0] in, output logic [2:0] out1, output logic [2:0] out2);
    assign out1 = in[1 +: 3];
    assign out2 = in[5 -: 3];
endmodule
module unpacked_array_sel(input logic [7:0] arr [0:3], input int idx, output logic [7:0] out);
    assign out = arr[idx];
endmodule
module unpacked_array_extract(input logic [7:0] arr [0:3], output logic [7:0] out);
    assign out = arr[2];
endmodule
module unpacked_array_plus_minus(input logic [7:0] arr [0:3], output logic [7:0] out1 [1:2], output logic [7:0] out2 [2:3]);
    assign out1 = arr[1 +: 2];
    assign out2 = arr[3 -: 2];
endmodule
module packed_array_sel(input logic [7:0][3:0] parr, input int idx, output logic [3:0] out);
    assign out = parr[idx];
endmodule
module packed_array_extract(input logic [7:0][3:0] parr, output logic [2:0] out);
    assign out = parr[3:1];
endmodule
module packed_array_plus_minus(input logic [7:0][3:0] parr, output logic [1:0] out1, output logic [1:0] out2);
    assign out1 = parr[1 +: 2];
    assign out2 = parr[2 -: 2];
endmodule
module assoc_array_sel(input int assoc_arr[string], input string key, output int out);
    always_comb begin
        out = assoc_arr[key];
    end
endmodule
module wildcard_array_sel(input logic [3:0] wild[*], input int idx, output logic [3:0] out);
    always_comb begin
        out = wild[idx];
    end
endmodule
module dyn_array_sel(input int dyn[], input int idx, output int out);
    always_comb begin
        out = dyn[idx];
    end
endmodule
module queue_array_sel(input int queue_arr[$], input int idx, output int out1, output int out2);
    always_comb begin
        out1 = queue_arr[$];
        out2 = queue_arr[$ - 1];
    end
endmodule
module queue_array_extract(input int queue_arr[$], output int slice_out[$]);
    always_comb begin
        slice_out = queue_arr[1:4];
    end
endmodule
module string_sel(input string s, input int idx, output byte out);
    always_comb begin
        out = s[idx];
    end
endmodule
typedef struct packed { logic [3:0] f1; logic [1:0] f2; } PackedStruct;
module struct_packed_sel(input PackedStruct sp, input int idx, output logic [1:0] out);
    assign out = sp.f1[idx +: 2];
endmodule
module struct_array_sel(input PackedStruct arr [0:3], input int idx, output logic [3:0] out);
    assign out = arr[idx].f1;
endmodule
module basic_extract(input logic [7:0] vec, output logic [2:0] out);
    assign out = vec[5:3];
endmodule
module selpm_basic_pack(input logic [7:0] vec, output logic [2:0] out1, output logic [2:0] out2);
    assign out1 = vec[2 +: 3];
    assign out2 = vec[4 -: 2];
endmodule
module selpm_basic_struct(input PackedStruct sp, output logic [1:0] out1, output logic [1:0] out2);
    assign out1 = sp.f1[1 +: 2];
    assign out2 = sp.f1[3 -: 2];
endmodule
module selpm_unpacked_extract(input logic [7:0] arr [0:3], output logic [7:0] out [0:0]);
    assign out = arr[0 +: 1];
endmodule
module queue_plus_minus(input int queue_arr[$], output int out1, output int out2);
    always_comb begin
        out1 = queue_arr[2];
        out2 = queue_arr[5];
    end
endmodule
module basic_plus_minus(input logic [7:0] in, output logic [3:0] out1, output logic [3:0] out2);
    assign out1 = in[0 +: 4];
    assign out2 = in[7 -: 4];
endmodule
