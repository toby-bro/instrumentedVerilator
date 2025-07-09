module sys_disp_task(
    input  logic [15:0] in_data,
    output logic [15:0] out_data
);
    always_comb begin
        out_data = in_data;
        $display("sys_disp_task value=%0d", in_data);
        $write("sys_disp_task (write) value=%0d\n", in_data);
        $strobe("sys_disp_task (strobe) value=%0d", in_data);
        $monitor("sys_disp_task monitor value=%0d", in_data);
    end
endmodule
module sys_file_task(
    input  logic [31:0] datain,
    output logic [31:0] dataout
);
    int fd = 1;
    always_comb begin
        dataout = datain;
        $fdisplay(fd, "file display = %0d", datain);
        $fwrite(fd, "file write = %0d\n", datain);
    end
endmodule
module sys_string_task(
    input  logic [7:0] din,
    output logic [7:0] dout
);
    string buf1;
    string buf2;
    always_comb begin
        dout = din;
        $swrite(buf1, "Value is %0d", din);
        $sformat(buf2, buf1, din);
    end
endmodule
module sys_cast_task(
    input  logic [3:0] in_v,
    output logic       cast_ok
);
    logic [3:0] out_v;
    always_comb begin
        cast_ok = 0;
        if ($cast(out_v, in_v))
            cast_ok = 1;
    end
endmodule
module sys_severity_task(
    input  logic [7:0] x,
    output logic [7:0] y
);
    always_comb begin
        y = x;
        if (x == 8'd0)
            $error("Zero encountered");
        else if (x == 8'd255)
            $warning("Max encountered");
        else
            $info("Value=%0d", x);
    end
endmodule
module sys_dump_task(
    input  logic enable,
    output logic done
);
    logic [7:0] dummy;
    always_comb begin
        dummy = enable;
        done  = dummy;
        $dumpfile("wave.vcd");
        $dumpvars(0, sys_dump_task);
        $dumpon;
        $dumpoff;
        $dumpall;
        $dumplimit(1024);
        $dumpflush;
    end
endmodule
module sys_mem_task(
    input  logic [7:0] in_data,
    output logic [7:0] out_data
);
    logic [7:0] mem [0:15];
    always_comb begin
        out_data = in_data;
        $readmemb("dummy.mem", mem);
        $readmemh("dummy.mem", mem);
        $writememb("out.mem", mem);
        $writememh("out.mem", mem);
    end
endmodule
module sys_time_mod(
    input  logic clk,
    output logic dummy
);
    always_comb begin
        dummy = clk;
        $timeformat(-9, 2, " ps", 10);
        $printtimescale(sys_time_mod);
    end
endmodule
module sys_assert_ctrl(
    input  logic in0,
    output logic out0
);
    always_comb begin
        out0 = in0;
        $assertcontrol(0);
        $asserton;
        $assertoff;
        $assertkill;
        $assertpasson;
        $assertpassoff;
        $assertfailon;
        $assertfailoff;
        $assertnonvacuouson;
        $assertvacuousoff;
    end
endmodule
module sys_stochastic(
    input  logic [31:0] a,
    output logic [31:0] b
);
    int q1, q2, q3, q_out;
    int ret;
    always_comb begin
        b   = a;
        q1  = a;
        q2  = a + 1;
        q3  = a + 2;
        $q_initialize(q1, q2, q3, q_out);
        $q_add(q1, q2, q3, q_out);
        $q_remove(q1, q_out, q2, q3);
        $q_exam(q1, q_out, q2, q3);
        ret = $q_full(q1, q_out);
    end
endmodule
module sys_sdf(
    input  logic [1:0] i,
    output logic [1:0] o
);
    always_comb begin
        o = i;
        $sdf_annotate("file.sdf");
    end
endmodule
module sys_scope_task(
    input  logic [7:0] in1,
    output logic [7:0] out1
);
    always_comb begin
        out1 = in1;
        $scope(sys_scope_task);
        $list;
    end
endmodule
module sys_showvars(
    input  logic [3:0] a,
    output logic [3:0] b
);
    reg [3:0] r;
    always_comb begin
        r = a;
        b = r;
        $showvars(r);
    end
endmodule
module sys_dumpports_task(
    input  logic [3:0] x,
    output logic [3:0] y
);
    always_comb begin
        y = x;
        $dumpports("ports.vcd");
        $dumpportson("ports.vcd");
        $dumpportsoff("ports.vcd");
        $dumpportsall("ports.vcd");
        $dumpportslimit(512, "ports.vcd");
        $dumpportsflush("ports.vcd");
    end
endmodule
module sys_system_task(
    input  logic [3:0] in,
    output logic [3:0] out
);
    always_comb begin
        out = in;
        $system("echo Hello");
    end
endmodule
