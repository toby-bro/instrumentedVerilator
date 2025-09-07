module unroll_genvar_ok #(parameter WIDTH = 8) (
    input  logic [WIDTH-1:0] in_data,
    output logic [WIDTH-1:0] out_data
);
    genvar i;
    generate
        /*verilator unroll_full*/
        for (i = 0; i < WIDTH; i = i + 1) begin : g_ok
            assign out_data[i] = in_data[i];
        end
    endgenerate
endmodule
module unroll_while_ok (
    input  logic        clk,
    input  logic        rst_n,
    input  logic [3:0]  in_bus,
    output logic [3:0]  out_bus
);
    always_ff @(posedge clk) begin
        if (!rst_n) begin
            out_bus <= '0;
        end else begin
            int idx;
            idx = 0;
            /*verilator unroll_full*/
            while (idx < 4) begin
                out_bus[idx] <= in_bus[idx];
                idx = idx + 1;
            end
        end
    end
endmodule
module unroll_while_bad_init (
    input  logic       clk,
    input  logic [3:0] seed,
    output logic [3:0] result
);
    always_ff @(posedge clk) begin
        int id;
        id = seed[1:0];           
        while (id < 4) begin
            result <= seed;
            id = id + 1;
        end
    end
endmodule
module unroll_while_fork (
    input  logic clk,
    input  logic in_sig,
    output logic out_sig
);
    always_ff @(posedge clk) begin
        int k;
        k = 0;
        while (k < 2) begin
            fork
                out_sig <= in_sig;
            join_any
            k = k + 1;
        end
    end
endmodule
module unroll_while_varmod (
    input  logic        clk,
    input  logic [1:0]  val,
    output logic [1:0]  out_val
);
    always_ff @(posedge clk) begin
        int i;
        i = 0;
        while (i < 2) begin
            out_val <= val;
            i       = i + 1;       
        end
    end
endmodule
module unroll_while_large (
    input  logic clk,
    output logic done
);
    logic [31:0] j_reg;
    always_ff @(posedge clk) begin
        int j;
        j = 0;
        while (j < 40) begin       
            j = j + 1;
        end
        j_reg <= j;
    end
    assign done = j_reg[0];
endmodule
module unroll_disabled (
    input  logic clk,
    input  logic in_data,
    output logic out_data
);
    always_ff @(posedge clk) begin
        int z;
        z = 0;
        /*verilator unroll_disable*/
        while (z < 3) begin        
            out_data <= in_data;
            z        = z + 1;
        end
    end
endmodule
