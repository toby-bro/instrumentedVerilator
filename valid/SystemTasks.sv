module severity_mod(
    input  logic in_sig,
    output logic out_sig
);
    always_comb begin
        out_sig = in_sig;
        if (in_sig)
            $error("in_sig asserted");
    end
endmodule
module cast_mod(
    input  logic [7:0] in_val,
    output logic [7:0] out_val
);
    int cast_ok;
    always_comb begin
        cast_ok = $cast(out_val, in_val);
    end
endmodule
module readmem_mod(
    input  logic en,
    output logic done
);
    logic [7:0] mem [0:15];
    initial begin
        $readmemh("dummy.hex", mem);
    end
    always_comb begin
        done = en;
    end
endmodule
module string_mod(
    input  logic clk,
    output logic done
);
    string str1;
    string str2;
    always_comb begin
        $sformat(str1, "CLK=%0d", clk);
        str2 = str1;
        done = clk;
    end
endmodule
module dump_mod(
    input  logic d,
    output logic y
);
    initial begin
        $dumpfile("wave.vcd");
        $dumpvars(0);
    end
    assign y = d;
endmodule
module scope_mod(
    input  logic dummy,
    output logic res
);
    assign res = dummy;
endmodule
module time_mod(
    input  logic in_bit,
    output logic out_bit
);
    time tcurr;
    always_comb begin
        tcurr = $time;
        out_bit = in_bit;
    end
endmodule
