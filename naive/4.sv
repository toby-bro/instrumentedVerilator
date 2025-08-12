module bitwise_ops_mod(
    input  logic [7:0] in_data,
    output logic [7:0] out_data
);
    always_comb begin
        out_data = {in_data[3:0], in_data[7:4]}; 
        out_data = ~out_data;                    
    end
endmodule
module param_gen_mod #(
    parameter WIDTH = 16
) (
    input  logic [WIDTH-1:0] in_bus,
    output logic             parity
);
    logic [WIDTH-1:0] parity_vec;
    genvar i;
    generate
        for (i = 0; i < WIDTH; i++) begin : g_par
            assign parity_vec[i] = in_bus[i];
        end
    endgenerate
    assign parity = ^parity_vec;
endmodule
module state_enum_mod(
    input  logic clk,
    input  logic rst_n,
    input  logic start,
    output logic busy
);
    typedef enum logic [1:0] {IDLE, RUN, DONE} state_t;
    state_t state, next_state;
    always_comb begin
        next_state = state;
        case (state)
            IDLE: if (start) next_state = RUN;
            RUN :           next_state = DONE;
            DONE:           next_state = IDLE;
            default:        next_state = IDLE;
        endcase
    end
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            state <= IDLE;
        else
            state <= next_state;
    end
    assign busy = (state == RUN);
endmodule
module struct_union_mod(
    input  logic [5:0] in_data,
    output logic [3:0] out_high,
    output logic [1:0] out_low
);
    typedef struct packed {
        logic [3:0] high;
        logic [1:0] low;
    } split_t;
    typedef union packed {
        logic [5:0] raw;
        split_t     s;
    } access_t;
    access_t u;
    always_comb begin
        u.raw    = in_data;
        out_high = u.s.high;
        out_low  = u.s.low;
    end
endmodule
module class_feature_mod(
    input  logic [3:0] in_val,
    output logic [3:0] out_val
);
    class multiplier_c;
        function int mult(int x);
            return x * 2;
        endfunction
    endclass
    always_comb begin
        multiplier_c c = new();
        out_val = c.mult(in_val);
    end
endmodule
module array_assoc_mod(
    input  logic [3:0] addr,
    output logic [7:0] data
);
    logic [7:0] mem[int];
    initial begin
        mem[0] = 8'hAA;
        mem[1] = 8'h55;
        mem[2] = 8'h0F;
        mem[3] = 8'hF0;
    end
    always_comb begin
        if (mem.exists(addr))
            data = mem[addr];
        else
            data = 8'h00;
    end
endmodule
