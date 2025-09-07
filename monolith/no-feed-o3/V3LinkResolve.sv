primitive nand_udp (out, a, b);
    output out;
    input  a, b;
    table
        0 0 : 1;
        0 1 : 1;
        1 0 : 1;
        1 1 : 0;
    endtable
endprimitive
module class_mod (
    input  logic in_sig,
    output logic out_sig
);
    class sample_c;
        rand  bit [3:0] x;
        randc bit [3:0] y;
        constraint soft_c { x inside {[0:15]}; }
        constraint dist_c { y dist { [0:15] :/ 16 }; }
        constraint order_c { solve x before y; }
        function new(); endfunction
    endclass
    sample_c c_inst = new();
    assign out_sig = in_sig;
endmodule
module init_auto_mod (
    input  logic in_sig,
    output logic out_sig
);
    logic reg_sig;
    initial automatic begin
        reg_sig = in_sig;
    end
    assign out_sig = reg_sig;
endmodule
module assert_mod (
    input  logic clk,
    output logic out_sig
);
    always_ff @(posedge clk) begin
        out_sig <= clk;
        assert (out_sig !== 1'bx);
    end
endmodule
let add2(a, b) = a + b;
module let_mod (
    input  logic [3:0] a,
    output logic [3:0] y
);
    assign y = add2(a, 4'd2);
endmodule
module pragma_mod (
    input  logic in_sig,
    output logic out_sig
);
    /* verilator coverage_block_off */
    begin : blk
        logic tmp;
        tmp = in_sig;
    end
    task automatic pub_tsk;
        out_sig = in_sig;
    endtask
    assign out_sig = in_sig;
endmodule
module fileops_mod (
    input  logic [7:0] din,
    output logic [7:0] dout
);
    integer fd;
    integer res;
    logic   [7:0] mem [0:255];
    logic   [7:0] tmp;
    string  str;
    initial automatic begin
        fd  = $fopen("dummy.txt", "r");
        res = $fscanf(fd, "%0d", tmp);
        res = $sscanf("42", "%0d", tmp);
        str = $sformatf("%0d", din);
        res = $fread(fd, mem);
        $ferror(fd);
        $feof(fd);
        $fclose(fd);
    end
    assign dout = tmp;
endmodule
module gen_mod #(
    parameter WIDTH = 4
) (
    input  logic [WIDTH-1:0] in_bus,
    output logic [WIDTH-1:0] out_bus
);
    generate
        genvar g;
        for (g = 0; g < WIDTH; g = g + 1) begin : g_loop
            if (g % 2 == 0) begin : even
                assign out_bus[g] = in_bus[g];
            end else begin : odd
                assign out_bus[g] = ~in_bus[g];
            end
        end
    endgenerate
endmodule
interface ifc;
    logic a;
    modport master (input a);
endinterface
module iface_mod (
    input  logic in_sig,
    output logic out_sig
);
    ifc.master mp_var;   
    assign out_sig = in_sig;
endmodule
module dpi_mod (
    input  logic in_sig,
    output logic out_sig
);
    import "DPI-C" context task dpi_external (input int x);
    export "DPI-C" task sv_task_impl;
    task sv_task_impl (input int y);
        out_sig = in_sig;
    endtask
    assign out_sig = in_sig;
endmodule
