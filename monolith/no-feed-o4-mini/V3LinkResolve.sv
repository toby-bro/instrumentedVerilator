interface MyIf(input logic sig_in, output logic sig_out);
    modport mp (input sig_in, output sig_out);
endinterface
primitive my_udp(out, in1, in2);
    output out; input in1, in2;
    table
        0 0 : 0;
        0 1 : 1;
        1 0 : 1;
        1 1 : 0;
    endtable
endprimitive
module feature_basic(input logic a, input logic [1:0] b, output logic c);
    assign c = a & b[0];
endmodule
module feature_class_constraint(input logic clk, input logic rst, output logic [3:0] a_out);
    class C;
        rand bit [3:0] a;
        rand bit [3:0] b;
        constraint c1 { a < b; }
        constraint c_dist { dist a { [0:1] :/1, [2:3] :/3 }; }
    endclass
    C c_inst;
    always_comb begin
        c_inst = new();
        void'(c_inst.randomize());
        a_out = c_inst.a;
    end
endmodule
module feature_cover_assert(input logic clk, input logic d, output logic q);
    always_ff @(posedge clk) q <= d;
    property p1 @(posedge clk) d |-> q;
    assert property(p1);
    cover property(p1);
endmodule
module feature_tasks(input logic [7:0] in, output logic [7:0] out);
    import "DPI-C" function int dpi_func(input int x);
    function int f1(input int x); return x + 1; endfunction
    task t1(input int y, output int z); z = y * 2; endtask
    always_comb begin
        int tmp;
        t1(in, tmp);
        out = f1(tmp) + dpi_func(tmp);
    end
endmodule
module feature_case_default(input logic [1:0] sel, input logic in0, input logic in1, input logic in2, output logic out);
    always_comb begin
        case (sel)
            2'b00: out = in0;
            2'b01: out = in1;
            default: out = in2;
        endcase
    end
endmodule
module feature_let(input logic a, input logic b, output logic y);
    let f = a & b;
    always_comb y = f;
endmodule
module feature_format(input logic [7:0] in, output logic [7:0] out);
    logic [31:0] tmp_str;
    integer ret;
    always_comb begin
        tmp_str = $sformatf("Val=%0d", in);
        ret = $sscanf(tmp_str, "%5c%d", out, out);
    end
endmodule
module feature_file_ops(input logic [7:0] in, output logic [7:0] out);
    integer fd;
    logic fe, feof_flag;
    always_comb begin
        fd = $fopen("file.txt", "r");
        feof_flag = $feof(fd);
        fe = $ferror(fd);
        $fclose(fd);
        out = feof_flag ? in : 8'hFF;
    end
endmodule
module feature_if(MyIf.mp if1, output logic out);
    assign out = if1.sig_in;
endmodule
module feature_gen(input logic en, output logic [3:0] out);
    genvar i;
    generate
        if (en) begin : GEN_IF
            logic [3:0] arr [0:3];
            for (i = 0; i < 4; i = i + 1) begin : GEN_FOR
                assign arr[i] = i;
            end
        end
    endgenerate
    assign out = en ? arr[2] : 4'b0;
endmodule
module feature_udp(input logic a, input logic b, output logic y);
    my_udp udp1(y, a, b);
endmodule
