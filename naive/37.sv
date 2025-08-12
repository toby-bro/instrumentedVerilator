module struct_example (
    input  logic [7:0] in,
    output logic [7:0] out
);
    typedef struct packed {
        logic [3:0] hi;
        logic [3:0] lo;
    } nibbles_t;
    function automatic nibbles_t split (input logic [7:0] val);
        nibbles_t s;
        s.hi = val[7:4];
        s.lo = val[3:0];
        return s;
    endfunction
    always_comb begin
        nibbles_t tmp = split(in);
        out = {tmp.lo, tmp.hi};
    end
endmodule
module union_enum_example #(
    parameter WIDTH = 16
) (
    input  logic                 clk,
    input  logic                 rst_n,
    input  logic [WIDTH-1:0]     din,
    output logic [WIDTH-1:0]     dout
);
    typedef enum logic [1:0] { S0, S1, S2, S3 } state_e;
    typedef union packed {
        logic [WIDTH-1:0] full;
        struct packed {
            logic [WIDTH/2-1:0] lower;
            logic [WIDTH/2-1:0] upper;
        } parts;
    } data_u;
    state_e state, next_state;
    data_u  data_reg, data_next;
    always_comb begin
        next_state = state;
        data_next  = data_reg;
        case (state)
            S0: begin
                data_next.full = din;
                next_state     = S1;
            end
            S1: begin
                data_next.full = {data_reg.parts.lower, data_reg.parts.upper};
                next_state     = S2;
            end
            S2: begin
                data_next.full = {~data_reg.parts.upper, ~data_reg.parts.lower};
                next_state     = S3;
            end
            default: begin
                next_state = S0;
            end
        endcase
    end
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state                <= S0;
            data_reg.full        <= '0;
        end else begin
            state                <= next_state;
            data_reg             <= data_next;
        end
    end
    assign dout = data_reg.full;
    property p_no_all_zeros;
        @(posedge clk) disable iff (!rst_n) dout != '0;
    endproperty
    assert property (p_no_all_zeros);
endmodule
module gen_loop_example #(
    parameter N = 4,
    parameter W = 8
) (
    input  logic [N*W-1:0] in_bus,
    output logic [N*W-1:0] out_bus
);
    logic [W-1:0] arr_in  [N];
    logic [W-1:0] arr_out [N];
    genvar i;
    generate
        for (i = 0; i < N; i++) begin : unpack
            assign arr_in[i]  = in_bus [i*W +: W];
            assign out_bus[i*W +: W] = arr_out[i];
        end
    endgenerate
    always_comb begin
        for (int j = 0; j < N; j++) begin
            arr_out[j] = ~arr_in[j];
        end
    end
endmodule
module class_example (
    input  logic       clk,
    input  logic       rst_n,
    input  logic [7:0] in_data,
    output logic [7:0] out_data
);
    class adder;
        int val;
        function new (int v = 0);
            val = v;
        endfunction
        function int add (int x);
            return val + x;
        endfunction
    endclass
    adder ad;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            ad       = new();
            out_data <= '0;
        end else begin
            if (ad == null) ad = new(5);
            out_data <= ad.add(in_data);
        end
    end
endmodule
module randomized_example (
    input  logic clk,
    input  logic rst_n,
    input  logic start,
    output logic done
);
    int counter;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            counter <= 0;
            done    <= 0;
        end else begin
            if (start) begin
                counter <= $urandom_range(0, 100);
                done    <= 1'b1;
            end else begin
                done    <= 1'b0;
            end
        end
    end
endmodule
module constraint_example (
    input  logic clk,
    input  logic rst_n,
    output logic [7:0] random_val
);
    class randomizer;
        rand logic [7:0] val;
        constraint c { val inside {[8'h00:8'hFF]}; }
    endclass
    randomizer r;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            r = new();
            random_val <= '0;
        end else begin
            if (r.randomize())
                random_val <= r.val;
        end
    end
endmodule
module covergroup_example (
    input  logic       clk,
    input  logic       rst_n,
    input  logic [3:0] a,
    output logic [3:0] b
);
    always_comb begin
        b = ~a;
    end
    covergroup cg @(posedge clk);
        coverpoint a;
    endgroup
    cg c0 = new();
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
        end
    end
endmodule
