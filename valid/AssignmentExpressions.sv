package my_types;
    typedef struct packed {
        logic [3:0] hi;
        logic [3:0] lo;
    } byte_parts_t;
endpackage
module simple_assigner (
    input  logic [7:0] in_data,
    output logic [7:0] out_data
);
    assign out_data = in_data;
endmodule
module compound_assigner (
    input  logic [7:0] in_val,
    output logic [7:0] out_val
);
    logic [7:0] temp;
    always_comb begin
        temp = '0;
        temp += in_val;
    end
    assign out_val = temp;
endmodule
module nonblocking_assigner (
    input  logic        clk,
    input  logic        rst,
    input  logic [7:0]  in_bus,
    output logic [7:0]  out_bus
);
    always_ff @(posedge clk or posedge rst) begin
        if (rst)
            out_bus <= '0;
        else
            out_bus <= in_bus;
    end
endmodule
module struct_pattern_assigner (
    input  logic [7:0]            in_vec,
    output my_types::byte_parts_t out_struct
);
    import my_types::*;
    always_comb begin
        out_struct = '{hi: in_vec[7:4], lo: in_vec[3:0]};
    end
endmodule
module array_pattern_assigner (
    input  logic [7:0] in_byte,
    output logic [7:0] arr_out [0:3]
);
    always_comb begin
        arr_out = '{4{in_byte}};
    end
endmodule
module structured_array_example (
    input  logic [7:0] idx0_val,
    input  logic [7:0] idx1_val,
    output logic [7:0] data_arr [0:1]
);
    always_comb begin
        data_arr = '{default: 8'hAA, 0: idx0_val, 1: idx1_val};
    end
endmodule
module replicated_pattern_assigner (
    input  logic       dummy_in,
    output logic [7:0] out_arr [0:1]
);
    always_comb begin
        out_arr = '{2{8'hFF}};
    end
endmodule
module child_unit (
    input  logic [7:0] in_port,
    output logic [7:0] out_port
);
    assign out_port = in_port;
endmodule
module array_instance_wrapper (
    input  logic [7:0] vec_in  [0:2][0:3],
    output logic [7:0] vec_out [0:2][0:3]
);
    child_unit inst_array [0:2][0:3] (
        .in_port (vec_in),
        .out_port(vec_out)
    );
endmodule
