module width_alignment_mod (
    input  logic [63:0] i64,
    input  logic [31:0] i32,
    input  logic [15:0] i16,
    input  logic [7:0]  i8,
    output logic [63:0] o64
);
    logic [7:0]  v8;
    logic [15:0] v16;
    logic [31:0] v32;
    logic [63:0] v64;
    always_comb begin
        v8  = i8;
        v16 = i16;
        v32 = i32;
        v64 = i64;
        o64 = v64
              ^ {32'h0, v32}
              ^ {48'h0, v16}
              ^ {56'h0, v8};
    end
endmodule
module array_mod (
    input  logic [3:0] idx,
    output logic [7:0] data
);
    logic [7:0] mem [0:15];   
    always_comb begin
        data = mem[idx];
    end
endmodule
module struct_union_mod (
    input  logic [7:0] in_byte,
    output logic [3:0] out_nibble
);
    typedef struct packed {
        logic [3:0] a;
        logic [3:0] b;
    } packed_t;
    typedef union packed {
        logic   [7:0] vec;
        packed_t      as_packed;
    } union_t;
    union_t u_var;
    always_comb begin
        u_var.vec  = in_byte;
        out_nibble = u_var.as_packed.a;
    end
endmodule
module enum_mod (
    input  logic [1:0] sel,
    output logic       lsb_out
);
    typedef enum logic [1:0] {
        S0 = 2'b00,
        S1 = 2'b01,
        S2 = 2'b10,
        S3 = 2'b11
    } state_t;
    state_t state_var;
    always_comb begin
        state_var = state_t'(sel);
        lsb_out   = state_var[0];
    end
endmodule
module clocked_mod (
    input  logic clk,
    input  logic rst_n,
    input  logic d,
    output logic q
);
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) q <= 1'b0;
        else        q <= d;
    end
endmodule
module dpi_call_mod (
    input  logic [31:0] in_data,
    output logic [31:0] out_data
);
    import "DPI-C" function int add_one (input int a);
    function automatic [31:0] inc32 (input [31:0] d);
        inc32 = add_one(d);
    endfunction
    always_comb begin
        out_data = inc32(in_data);
    end
endmodule
module multidim_array_mod (
    input  logic [1:0] sel1,
    input  logic [1:0] sel2,
    output logic [3:0] data
);
    logic [3:0] matrix [0:3][0:3];
    always_comb begin
        data = matrix[sel1][sel2];
    end
endmodule
module generated_vars_mod #(
    parameter int N = 4
) (
    input  logic [N-1:0] i_data,
    output logic [N-1:0] o_data
);
    genvar gi;
    generate
        for (gi = 0; gi < N; gi++) begin : gen_block
            logic temp;
            always_comb begin
                temp       = i_data[gi];
                o_data[gi] = temp;
            end
        end
    endgenerate
endmodule
