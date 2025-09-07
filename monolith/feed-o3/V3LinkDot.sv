interface my_if (input logic clk);
    logic sig;
    modport mp (input sig);
endinterface
package my_pkg;
    typedef logic [7:0] byte_t;
    function automatic byte_t invert(byte_t v); invert = ~v; endfunction
endpackage
module mod_iface_port (input  logic clk,
                       input  logic in1,
                       output logic out1);
    my_if intf(clk);
    assign intf.sig = in1;
    always_comb begin
        out1 = in1 & intf.sig;
    end
endmodule
module mod_param_class #(parameter WIDTH = 8)
                        (input  logic                     clk,
                         input  logic                     rst,
                         output logic [WIDTH-1:0]         data_o);
    typedef struct packed {logic [WIDTH-1:0] val;} my_struct_t;
    class ParamClass #(type T = int);
        T value;
        function void set_default(); value = '0; endfunction
    endclass
    ParamClass #(my_struct_t) obj;
    always_ff @(posedge clk) begin
        if (rst) begin
            obj = new();
            obj.set_default();
            data_o <= '0;
        end else begin
            data_o <= obj.value.val;
        end
    end
endmodule
module mod_enum_typedef (input  logic [1:0] sel,
                         output logic        flag);
    typedef enum logic [1:0] {IDLE = 2'b00, BUSY = 2'b01, DONE = 2'b10} state_e;
    state_e state;
    always_comb begin
        state = state_e'(sel);
        flag  = (state == DONE);
    end
endmodule
module mod_generate (input  logic [3:0] vec_in,
                     output logic [3:0] vec_out);
    genvar i;
    generate
        for (i = 0; i < 4; i++) begin : genblk
            assign vec_out[i] = vec_in[3 - i];
        end
    endgenerate
endmodule
module mod_clocking (input  logic clk,
                     input  logic d,
                     output logic q);
    logic q_reg;
    clocking cb @(posedge clk);
        input  d;
        output q_reg;
    endclocking
    always_ff @(posedge clk) begin
        q_reg <= d;
    end
    assign q = q_reg;
endmodule
module mod_constraint (input  logic clk,
                       output logic [7:0] rdata);
    class RandClass;
        rand bit [7:0] data;
        constraint c_data { data inside {[8'd10:8'd20]}; }
    endclass
    RandClass obj;
    logic [7:0] data_reg;
    always_ff @(posedge clk) begin
        if (!obj) obj = new();
        if (obj.randomize()) data_reg <= obj.data;
    end
    assign rdata = data_reg;
endmodule
module mod_foreach (input  logic [3:0][3:0] matrix_in,
                    output logic [3:0]       sum_out);
    int idx;
    always_comb begin
        sum_out = '0;
        foreach (matrix_in[idx]) begin
            sum_out[idx] = ^matrix_in[idx];
        end
    end
endmodule
module mod_disable (input  logic clk,
                    input  logic en,
                    output logic done);
    logic [3:0] cnt;
    always_ff @(posedge clk) begin : count_blk
        if (!en) begin
            disable count_blk;
        end else begin
            cnt <= cnt + 1;
        end
    end
    assign done = &cnt;
endmodule
module mod_fwd_typedef (input  logic in_sig,
                        output logic out_sig);
    typedef struct packed {logic a;} st_t;
    typedef st_t st_fwd_t;
    st_fwd_t var_struct;
    always_comb begin
        var_struct.a = in_sig;
        out_sig      = var_struct.a;
    end
endmodule
module mod_pkg_use (input  logic [7:0] d_in,
                    output logic [7:0] d_out);
    import my_pkg::*;
    assign d_out = invert(d_in);
endmodule
module mod_task (input  logic clk,
                 input  logic a,
                 output logic b);
    task automatic t_compute(input logic x, output logic y);
        y = ~x;
    endtask
    always_ff @(posedge clk) begin
        t_compute(a, b);
    end
endmodule
