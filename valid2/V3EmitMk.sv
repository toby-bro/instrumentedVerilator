package util_pkg;
    function automatic logic [15:0] swap16(input logic [15:0] v);
        return {v[7:0], v[15:8]};
    endfunction
endpackage
module struct_logic(
    input  logic [7:0]  in_data,
    output logic [15:0] out_data
);
    typedef struct packed {
        logic [3:0] lo;
        logic [3:0] hi;
    } byte_s;
    byte_s b;
    always_comb begin
        b.lo      = in_data[3:0];
        b.hi      = in_data[7:4];
        out_data  = {b.hi, b.lo};
    end
endmodule
module enum_fsm(
    input  logic clk,
    input  logic rst_n,
    input  logic in_sig,
    output logic out_sig
);
    typedef enum logic [1:0] {S0, S1, S2} state_t;
    state_t state, next;
    always_comb begin
        next    = state;
        out_sig = 1'b0;
        unique case (state)
            S0: if (in_sig) next = S1;
            S1: begin
                    out_sig = 1'b1;
                    next    = in_sig ? S2 : S0;
                end
            S2: next = S0;
            default: next = S0;
        endcase
    end
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            state <= S0;
        else
            state <= next;
    end
endmodule
module class_proc(
    input  logic [3:0] a,
    output logic [3:0] y
);
    class helper;
        function logic [3:0] double(input logic [3:0] val);
            return val << 1;
        endfunction
    endclass
    helper h;
    always_comb begin
        h = new();
        y = h.double(a);
    end
endmodule
module array_concat(
    input  logic [3:0] in_a,
    input  logic [3:0] in_b,
    output logic [7:0] out_concat
);
    logic [3:0] vec [0:1];
    always_comb begin
        vec[0]     = in_a;
        vec[1]     = in_b;
        out_concat = {vec[0], vec[1]};
    end
endmodule
module union_pack(
    input  logic [31:0] din,
    output logic [31:0] dout
);
    typedef union packed {
        logic [31:0] word;
        struct packed {
            logic [15:0] lo;
            logic [15:0] hi;
        } halves;
    } u_t;
    u_t uval;
    always_comb begin
        uval.word = din;
        dout      = {uval.halves.hi, uval.halves.lo};
    end
endmodule
module generate_block #(parameter WIDTH = 4) (
    input  logic [WIDTH-1:0] in_vec,
    output logic [WIDTH-1:0] out_vec
);
    genvar i;
    generate
        for (i = 0; i < WIDTH; i++) begin : gen_assign
            assign out_vec[i] = ~in_vec[i];
        end
    endgenerate
endmodule
interface simple_bus #(parameter W = 8) ();
    logic [W-1:0] data;
    modport master (output data);
    modport slave  (input  data);
endinterface
module interface_master(
    input  logic [7:0] in_val,
    output logic       dummy_out
);
    simple_bus #(8) bus_if();
    assign bus_if.data = in_val;
    assign dummy_out   = bus_if.data[0];
endmodule
module interface_slave(
    input  logic       drive_enable,
    output logic [7:0] out_val
);
    simple_bus #(8) bus_if();
    assign out_val = drive_enable ? bus_if.data : '0;
endmodule
module assert_cover(
    input  logic clk,
    input  logic rst_n,
    input  logic cond_i,
    output logic asserted_o
);
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            asserted_o <= 1'b0;
        end else begin
            asserted_o <= cond_i;
            assert (cond_i == asserted_o);
            cover  (cond_i && asserted_o);
        end
    end
endmodule
module package_user(
    input  logic [15:0] din,
    output logic [15:0] dout
);
    import util_pkg::*;
    assign dout = swap16(din);
endmodule
