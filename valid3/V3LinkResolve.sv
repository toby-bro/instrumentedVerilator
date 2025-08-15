primitive nand_udp (out, a, b);
    output out;
    input  a, b;
    table
        0 ? : 1;
        1 0 : 1;
        1 1 : 0;
    endtable
endprimitive
module constraints_mod(
    input  logic        clk,
    output logic [3:0]  random_out
);
    class rand_cls;
        rand  bit [3:0] val;
        rand  bit [3:0] other;
        randc bit [3:0] cyc;
        constraint soft_c { soft val inside { [0:15] }; }
    endclass
    rand_cls rc_h;
    always_ff @(posedge clk) begin
        if (rc_h == null) rc_h <= new();
        void'(rc_h.randomize());
        random_out <= rc_h.val;
    end
endmodule
module dpi_mod(
    input  logic [31:0] in_val,
    output logic [31:0] out_val
);
    import "DPI-C" function int c_func(input int a);
    export "DPI-C" function sv_add;
    function int sv_add(input int x);
        sv_add = x + 1;
    endfunction
    task automatic my_task(input logic x);
    endtask
    always_comb begin
        out_val = c_func(in_val) + sv_add(in_val);
        my_task(out_val[0]);
    end
endmodule
module let_mod(
    input  logic [7:0] a_in,
    output logic [7:0] a_out
);
    let add1(x) = (x + 1);
    assign a_out = add1(a_in);
endmodule
module fileop_mod(
    input  logic trig,
    output logic success
);
    integer fd;
    integer c;
    integer eof_flag;
    integer err_flag;
    string  text;
    string  out_str;
    integer parsed_val;
    integer dummy;
    always_ff @(posedge trig) begin
        fd <= $fopen("foo.txt", "r");
        success <= (fd != 0);
        if (fd) begin
            c        <= $fgetc(fd);
            eof_flag <= $feof(fd);
            err_flag <= $ferror(fd, text);
            parsed_val <= 0;
            dummy      <= 0;
            void'($fscanf(fd, "%s %d", text, parsed_val));
            out_str  <= $sformatf("val=%0d", parsed_val);
            void'($sscanf(out_str, "val=%d", dummy));
            void'($fclose(fd));
        end
    end
endmodule
module assert_mod(
    input  logic clk,
    input  logic a,
    input  logic b,
    output logic dummy
);
    property p1; @(posedge clk) a |=> b; endproperty
    property p2; @(posedge clk) (!a) |=> b; endproperty
    assert property(p1);
    assert property(p2);
    assign dummy = a & b;
endmodule
module generate_mod#(
    parameter int N = 4
)(
    input  logic [N-1:0] in_bus,
    output logic [N-1:0] out_bus
);
    genvar i;
    generate
        for (i = 0; i < N; i = i + 1) begin : gen_loop
            assign out_bus[i] = in_bus[i];
        end
    endgenerate
endmodule
interface simple_if(input logic clk);
    logic data;
    modport m (input  data, input clk);
    modport s (output data, input clk);
endinterface
module interface_mod(
    input  logic clk,
    output logic out_sig
);
    simple_if if_inst(clk);
    virtual simple_if.m master_port;
    assign out_sig = if_inst.data;
endmodule
module public_sig_mod(
    input  logic in_sig,
    output logic out_sig
);
    logic pub_sig /* verilator public */;
    always_comb begin
        pub_sig = in_sig;
        out_sig = pub_sig;
    end
endmodule
