package pack1;
typedef logic [7:0] byte_t;
endpackage
module enum_range_mod(
    input  logic clk,
    input  logic [3:0] in_data,
    output logic [3:0] out_data
);
    typedef enum logic [1:0] {STATE_IDLE[0:1], STATE_RUN[2:3]} state_e;
    state_e state;
    always_ff @(posedge clk) begin
        if (in_data[0]) state <= STATE_RUN2;
        else            state <= STATE_IDLE0;
    end
    assign out_data = {2'b0, state};
endmodule
module struct_implicit_mod(
    input  logic clk,
    input  logic d,
    output logic q
);
    struct packed {logic val;} s0, s1;
    always_ff @(posedge clk) begin
        if (d)  s0.val <= 1'b1;
        else    s0.val <= 1'b0;
        s1 <= s0;
    end
    assign q = s1.val;
endmodule
module task_lifetime_mod(
    input  logic clk,
    input  logic [15:0] data_in,
    output logic [15:0] data_out
);
    int counter;
    function automatic int add_one (input int v);
        static int local_static = 0;
        local_static++;
        return v + local_static;
    endfunction
    always_ff @(posedge clk) begin
        counter <= add_one(counter) + data_in;
    end
    assign data_out = counter;
endmodule
module generate_mod #(
    parameter int WIDTH = 8
)(
    input  logic clk,
    input  logic [WIDTH-1:0] in_bus,
    output logic [WIDTH-1:0] out_bus
);
    generate
        if (WIDTH == 8) begin : gen_block_if
            logic [WIDTH-1:0] r;
            always_ff @(posedge clk) r <= in_bus;
            assign out_bus = r;
        end
        else begin : gen_block_else
            logic [WIDTH-1:0] r;
            always_ff @(posedge clk) r <= in_bus;
            assign out_bus = r;
        end
        for (genvar i = 0; i < 1; i++) begin : gen_for
        end
        case (WIDTH)
            4  : begin : gen_case_small end
            8  : begin : gen_case_mid   end
            default: begin : gen_case_def end
        endcase
    endgenerate
endmodule
module loop_mod(
    input  logic clk,
    input  logic rst,
    output logic done
);
    logic [7:0] mem [0:9];
    int idx;
    always_ff @(posedge clk) begin
        if (rst) begin
            idx <= 0;
            foreach (mem[i]) mem[i] <= i;
        end
        else begin
            idx <= idx + 1;
            repeat (1) begin
                if (idx > 9) idx <= 0;
            end
        end
    end
    always_comb begin
        int acc = 0;
        int j = 0;
        do begin
            acc = acc + mem[j];
            j++;
        end while (j < 10);
    end
    always @(posedge clk) begin
        wait (idx == 10);
    end
    assign done = (idx == 10);
endmodule
module clocking_mod(
    input  logic clk,
    input  logic din,
    output logic dout
);
    clocking cb @(posedge clk);
        input  din;
        output dout;
    endclocking
    always @(cb) begin
        cb.dout <= cb.din;
    end
endmodule
module attribute_mod(
    input  logic clk,
    input  logic [3:0] data_in,
    output logic [3:0] data_out
);
    (* verilator public_flat        *) logic [3:0] flat_sig;
    (* verilator public_flat_rw     *) logic [3:0] flat_sig_rw;
    (* verilator public_flat_rd     *) logic [3:0] flat_sig_rd;
    (* verilator forceable          *) logic [3:0] force_sig;
    (* verilator isolate_assignments*) logic [3:0] isolate_sig;
    (* verilator sformat            *) string      str_sig;
    (* verilator split_var          *) logic [7:0] split_sig;
    (* verilator sc_bv              *) logic [3:0] bv_sig;
    (* verilator clocker            *) logic       clkr_sig;
    (* verilator no_clocker         *) logic       noclkr_sig;
    always_ff @(posedge clk) begin
        flat_sig      <= data_in;
        flat_sig_rw   <= data_in;
        flat_sig_rd   <= flat_sig;
        force_sig     <= data_in;
        isolate_sig   <= data_in;
        split_sig     <= {data_in, data_in};
        bv_sig        <= data_in;
        clkr_sig      <= clk;
        noclkr_sig    <= clk;
        str_sig       <= $sformatf("%0d", data_in);
    end
    assign data_out = flat_sig_rw;
endmodule
module eventcontrol_mod(
    input  logic clk,
    input  logic in_sig,
    output logic out_sig
);
    logic toggle;
    always begin
        @(posedge clk);
        toggle <= ~toggle;
    end
    assign out_sig = toggle ^ in_sig;
endmodule
module paramtype_mod #(
    parameter type T = int
)(
    input  logic clk,
    input  T din,
    output T dout
);
    T reg_t;
    always_ff @(posedge clk) begin
        reg_t <= din;
    end
    assign dout = reg_t;
endmodule
module class_mod(
    input  logic clk,
    input  logic in_sig,
    output logic out_sig
);
    class base;
        int b;
        function new(); b = 0; endfunction
    endclass
    class derived extends base;
        int d;
        function new();
            super.new();
            d = 1;
        endfunction
    endclass
    derived obj;
    always_ff @(posedge clk) begin
        if (obj == null) begin
            obj <= new();
        end
    end
    assign out_sig = in_sig;
endmodule
module package_use_mod(
    input  logic clk,
    input  pack1::byte_t d_i,
    output pack1::byte_t d_o
);
    import pack1::*;
    pack1::byte_t r;
    always_ff @(posedge clk) begin
        r <= d_i;
    end
    assign d_o = r;
endmodule
