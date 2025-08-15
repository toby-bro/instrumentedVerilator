module inline_func_mod(
    input  logic [7:0] in_a,
    output logic [7:0] out_y
);
    function automatic logic [7:0] double_val(input logic [7:0] i);
        double_val = i * 2;
    endfunction
    always_comb begin
        out_y = double_val(in_a);
    end
endmodule
module noinline_task_mod(
    input  logic [15:0] in_v,
    output logic [15:0] out_v
);
    task automatic scale2(input logic [15:0] vin, output logic [15:0] vout);
        vout = vin * 2;
    endtask
    always_comb begin
        scale2(in_v, out_v);
    end
endmodule
module ref_swap_mod(
    input  logic        clk,
    input  logic [31:0] in_x,
    input  logic [31:0] in_y,
    output logic [31:0] out_x,
    output logic [31:0] out_y
);
    task automatic do_swap(ref logic [31:0] a_ref, ref logic [31:0] b_ref);
        logic [31:0] tmp;
        tmp = a_ref;
        a_ref <= b_ref;
        b_ref <= tmp;
    endtask
    logic [31:0] reg_x, reg_y;
    always_ff @(posedge clk) begin
        reg_x <= in_x;
        reg_y <= in_y;
        do_swap(reg_x, reg_y);
        out_x <= reg_x;
        out_y <= reg_y;
    end
endmodule
module dpi_export_mod(
    input  logic [31:0] in_val,
    output logic        dummy
);
    function int sv_add_one(input int a_val);
        sv_add_one = a_val + 1;
    endfunction
    export "DPI-C" function sv_add_one;
    always_comb dummy = 1'b0;
endmodule
module dpi_import_mod(
    input  int in_a,
    input  int in_b,
    output int sum
);
    import "DPI-C" function int c_add(input int x, input int y);
    always_comb sum = c_add(in_a, in_b);
endmodule
module class_method_mod(
    input  logic       clk,
    input  logic [7:0] din,
    output logic [7:0] dout
);
    class my_class;
        logic [7:0] data;
        function new(input logic [7:0] d = 0);
            data = d;
        endfunction
        function logic [7:0] get();
            return data;
        endfunction
        task automatic set(input logic [7:0] v);
            data = v;
        endtask
    endclass
    my_class obj = new();
    always_ff @(posedge clk) begin
        obj.set(din);
        dout <= obj.get();
    end
endmodule
module open_array_mod#(
    parameter int SIZE = 4
)(
    input  int in_data [SIZE],
    output int out_sum
);
    function automatic int sum_array(input int arr[], input int len);
        int acc;
        int idx;
        acc = 0;
        for (idx = 0; idx < len; idx++) begin
            acc += arr[idx];
        end
        return acc;
    endfunction
    always_comb out_sum = sum_array(in_data, SIZE);
endmodule
module inout_port_mod(
    inout  wire  [7:0] bus,
    input  logic       dir,
    output logic [7:0] read_val
);
    assign bus = dir ? 8'hZZ : 8'hA5;
    always_comb read_val = bus;
endmodule
module default_arg_func_mod(
    input  logic [15:0] a,
    output logic [15:0] y
);
    function automatic logic [15:0] add_default(
        input logic [15:0] x,
        input logic [15:0] b_def = 16'd5
    );
        add_default = x + b_def;
    endfunction
    always_comb y = add_default(a);
endmodule
