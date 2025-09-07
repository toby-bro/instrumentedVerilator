module erase_mod #(parameter int N = 8) (
    input  logic [31:0] key,
    input  logic [31:0] arr [0:N-1],
    output logic [31:0] count_out
);
    always_comb begin
        count_out = 0;
        for (int i = 0; i < N; i++) begin
            if (arr[i] == key) begin
                count_out = count_out + 1;
            end
        end
    end
endmodule
module find_dup_mod #(parameter int N = 8) (
    input  logic [31:0] key,
    input  logic [31:0] arr [0:N-1],
    input  logic         check_enable,
    output logic [$clog2(N)-1:0] dup_index,
    output logic                 found
);
    logic found_flag;
    always_comb begin
        dup_index  = '0;
        found_flag = 0;
        for (int i = 0; i < N; i++) begin
            if (!found_flag) begin
                if (arr[i] != key && check_enable) begin
                    dup_index  = i;
                    found_flag = 1;
                end
            end
        end
        found = found_flag;
    end
endmodule
module dump_stats_mod #(parameter int N = 8, parameter int MAX_VAL = 8) (
    input  logic [31:0] data  [0:N-1],
    output logic [31:0] stats [0:MAX_VAL-1]
);
    int dist[int];
    always_comb begin
        dist.delete();
        foreach (data[j]) begin
            if (data[j] < MAX_VAL) dist[data[j]]++;
        end
        for (int k = 0; k < MAX_VAL; k++) begin
            stats[k] = dist.exists(k) ? dist[k] : 0;
        end
    end
endmodule
module dump_file_prefixed_mod #(parameter int N = 8) (
    input  logic         enable,
    input  logic [31:0]  data      [0:N-1],
    output logic [31:0]  stats_out [0:N-1]
);
    always_comb begin
        if (enable) begin
            logic [31:0] temp [0:N-1];
            foreach (data[i]) begin
                temp[i] = data[i] ^ 32'hDEADBEEF;
            end
            for (int m = 0; m < N; m++) begin
                stats_out[m] = temp[m];
            end
        end else begin
            for (int m = 0; m < N; m++) begin
                stats_out[m] = 0;
            end
        end
    end
endmodule
module debug_mod (
    input  logic [31:0] a,
    input  logic [31:0] b,
    output logic        debug_out
);
    function bit debug();
        debug = (a == b);
    endfunction
    function bit dumpLevel();
        dumpLevel = 1;
    endfunction
    assign debug_out = debug() & dumpLevel();
endmodule
module union_enum_struct_mod (
    input  logic [1:0]  selector,
    input  logic [7:0]  x_in,
    input  logic [7:0]  y_in,
    output logic [15:0] out
);
    typedef enum logic [1:0] {E_A = 2'd0, E_B = 2'd1, E_C = 2'd2} EType;
    typedef struct packed { logic [7:0] x; logic [7:0] y; } SType;
    union packed { SType s; logic [15:0] u; } UType;
    UType uvar;
    always_comb begin
        case (selector)
            E_A: begin
                uvar.s = '{x_in, y_in};
                out = uvar.u;
            end
            E_B: begin
                uvar.u = {x_in, y_in};
                out = uvar.s.x + uvar.s.y;
            end
            default: begin
                uvar.u = 16'hFFFF;
                out = uvar.u;
            end
        endcase
    end
endmodule
module generate_mod (
    input  logic [1:0] idx,
    output logic       val
);
    localparam int WIDTH = 4;
    logic [WIDTH-1:0] gen_array;
    genvar i;
    generate
        for (i = 0; i < WIDTH; i++) begin : GEN_LOOP
            assign gen_array[i] = i;
        end
    endgenerate
    assign val = gen_array[idx];
endmodule
