module selbit_packed (
    input  logic [31:0] in_bus,
    input  logic  [4:0] idx,
    output logic        bit_out
);
    assign bit_out = in_bus[idx];
endmodule
module selbit_unpacked (
    input  logic [7:0] in_bus0,
    input  logic [7:0] in_bus1,
    input  logic [7:0] in_bus2,
    input  logic [7:0] in_bus3,
    input  logic [1:0] idx,
    output logic [7:0] out_byte
);
    logic [7:0] arr [0:3];
    always_comb begin
        arr[0] = in_bus0;
        arr[1] = in_bus1;
        arr[2] = in_bus2;
        arr[3] = in_bus3;
        out_byte = arr[idx];
    end
endmodule
module selplus_slice (
    input  logic [31:0] bus,
    input  logic  [4:0] idx,
    output logic  [3:0] slice_out
);
    assign slice_out = bus[idx +: 4];
endmodule
module selminus_slice (
    input  logic [31:0] bus,
    input  logic  [4:0] idx,
    output logic  [3:0] slice_out
);
    assign slice_out = bus[idx -: 4];
endmodule
module selextract_const (
    input  logic [31:0] bus,
    output logic  [7:0] slice_out
);
    assign slice_out = bus[15:8];
endmodule
module selextract_ascending (
    input  logic [0:31] bus,
    output logic  [7:0] slice_out
);
    assign slice_out = bus[8:15];
endmodule
module packed_array_select (
    input  logic [3:0] idx,
    output logic [7:0] out_byte
);
    logic [3:0][7:0] packedVec;   
    assign out_byte = packedVec[idx];
endmodule
module queue_select (
    input  logic [7:0] dummy_in,
    output logic [7:0] out_byte
);
    byte q[$];                    
    always_comb begin
        out_byte = q[$ - 1];
    end
endmodule
module string_index (
    input  logic [7:0] idx,
    output logic [7:0] char_out
);
    string s;
    always_comb begin
        char_out = s[idx];
    end
endmodule
module dyn_array_select (
    input  logic [31:0] idx,
    output logic  [7:0] out_byte
);
    logic [7:0] dyn [];
    always_comb begin
        out_byte = dyn[idx];
    end
endmodule
module assoc_array_select (
    input  int unsigned key_in,
    output logic [7:0] out_byte
);
    logic [7:0] assoc [int];
    always_comb begin
        out_byte = assoc[key_in];
    end
endmodule
module wildcard_array_select (
    input  logic [31:0] idx,
    output logic [7:0] out_byte
);
    logic [7:0] wildcard_array[*];
    always_comb begin
        out_byte = wildcard_array[idx];
    end
endmodule
module struct_bit_select (
    input  logic [1:0] idx,
    output logic       bit_out
);
    typedef struct packed {
        logic a;
        logic b;
        logic c;
    } my_struct_t;
    my_struct_t s;
    assign bit_out = s[idx];
endmodule
