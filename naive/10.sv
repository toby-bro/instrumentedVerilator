module basic_arith #(parameter WIDTH = 8)(
    input  logic [WIDTH-1:0] a,
    input  logic [WIDTH-1:0] b,
    output logic [WIDTH:0]   sum,
    output logic [(2*WIDTH)-1:0] prod
);
    always_comb begin
        sum  = a + b;
        prod = a * b;
    end
endmodule
module enum_fsm (
    input  logic clk,
    input  logic rst_n,
    input  logic start,
    output logic done
);
    typedef enum logic [1:0] {S_IDLE, S_RUN, S_DONE} state_t;
    state_t state, next;
    always_comb begin
        next = state;
        done = 1'b0;
        unique case (state)
            S_IDLE: if (start) next = S_RUN;
            S_RUN : next = S_DONE;
            S_DONE: begin
                done = 1'b1;
                if (!start) next = S_IDLE;
            end
            default: next = S_IDLE;
        endcase
    end
    always_ff @(posedge clk, negedge rst_n) begin
        if (!rst_n)
            state <= S_IDLE;
        else
            state <= next;
    end
endmodule
module struct_mux (
    input  logic             sel,
    input  logic [31:0]      data_a,
    input  logic [31:0]      data_b,
    output logic [31:0]      data_o
);
    typedef struct packed {
        logic [31:0] data;
    } packet_t;
    packet_t pa, pb, po;
    always_comb begin
        pa.data = data_a;
        pb.data = data_b;
        if (sel)
            po = pa;
        else
            po = pb;
        data_o = po.data;
    end
endmodule
module array_reduce (
    input  logic [15:0] d0,
    input  logic [15:0] d1,
    input  logic [15:0] d2,
    input  logic [15:0] d3,
    output logic [15:0] and_out,
    output logic [15:0] or_out
);
    logic [15:0] arr [0:3];
    always_comb begin
        arr[0] = d0;
        arr[1] = d1;
        arr[2] = d2;
        arr[3] = d3;
        and_out = 16'hFFFF;
        or_out  = 16'h0000;
        for (int i = 0; i < 4; i++) begin
            and_out &= arr[i];
            or_out  |= arr[i];
        end
    end
endmodule
module generate_logic #(parameter WIDTH = 4)(
    input  logic [WIDTH-1:0] in_vec,
    output logic [WIDTH-1:0] inv_vec
);
    genvar i;
    generate
        for (i = 0; i < WIDTH; i++) begin : gen_inv
            always_comb inv_vec[i] = ~in_vec[i];
        end
    endgenerate
endmodule
module class_demo (
    input  logic [7:0] din,
    output logic [7:0] dout
);
    class incrementer;
        function automatic logic [7:0] inc(logic [7:0] x);
            return x + 8'd1;
        endfunction
    endclass
    always_comb begin
        automatic incrementer inc_obj = new();
        dout = inc_obj.inc(din);
    end
endmodule
module assertions_module (
    input  logic        clk,
    input  logic [3:0]  counter,
    output logic        overflow
);
    always_comb overflow = (counter == 4'hF);
    property no_overflow_p;
        @(posedge clk) counter != 4'hF;
    endproperty
    assert property (no_overflow_p);
endmodule
