module sel_basic (
    input  logic [7:0] data_i,
    input  logic [2:0] idx_i,
    output logic       bit_o,
    output logic [3:0] plus_o,
    output logic [3:0] minus_o
);
    always_comb begin
        bit_o   = data_i[idx_i];      
        plus_o  = data_i[idx_i +: 4]; 
        minus_o = data_i[idx_i -: 4]; 
    end
endmodule
module sel_unpacked_array (
    input  logic [7:0] data_i,
    input  logic [1:0] sel_i,
    output logic [7:0] elem_o
);
    logic [7:0] uarr [0:3];
    assign uarr[0] =  data_i;
    assign uarr[1] = ~data_i;
    assign uarr[2] = {data_i[3:0], data_i[7:4]};
    assign uarr[3] = 8'hA5;
    always_comb begin
        elem_o = uarr[sel_i];  
    end
endmodule
module sel_packed_array (
    input  logic [7:0] byte_i,
    input  logic [0:0] idx_i,
    output logic [7:0] elem_o,
    output logic [15:0] slice_o
);
    logic [1:0][7:0] parr;
    assign parr[0] =  byte_i;
    assign parr[1] = ~byte_i;
    always_comb begin
        elem_o  = parr[idx_i]; 
        slice_o = parr[1:0];   
    end
endmodule
module sel_ascending_vector (
    input  logic [0:7] asc_i,   
    input  logic [2:0] idx_i,
    output logic       bit_o
);
    assign bit_o = asc_i[idx_i];
endmodule
module sel_range_basic (
    input  logic [15:0] vec_i,
    output logic [7:0]  slice_o
);
    assign slice_o = vec_i[15:8]; 
endmodule
module sel_plus_minus_packed (
    input  logic [31:0] vec_i,
    input  logic [4:0]  base_i,
    output logic [15:0] plus_o,
    output logic [15:0] minus_o
);
    assign plus_o  = vec_i[base_i +: 16];   
    assign minus_o = vec_i[base_i -: 16];   
endmodule
module sel_queue_back (
    input  logic [7:0] dummy_i,
    output logic [7:0] last_o,
    output logic [7:0] back1_o
);
    logic [7:0] q[$];
    always_comb begin
        last_o  = q[$];        
        back1_o = q[$ - 1];    
    end
endmodule
module sel_string_char (
    input  int  idx_i,
    output byte char_o
);
    string str;
    always_comb begin
        char_o = str[idx_i];   
    end
endmodule
module sel_dynamic_array (
    input  logic [7:0] data_i,
    input  int         idx_i,
    output logic [7:0] elem_o
);
    logic [7:0] darr[];
    always_comb begin
        elem_o = darr[idx_i];  
    end
endmodule
