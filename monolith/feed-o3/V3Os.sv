module rand64_module (
    input  logic        clk,
    input  logic        rnd_en,
    output logic [63:0] random_value
);
    class rand_class;
        rand bit [63:0] value;
    endclass
    rand_class rc;
    always_ff @(posedge clk) begin
        if (rc == null) rc = new();
        if (rnd_en) begin
            void'(rc.randomize());
            random_value <= rc.value;
        end
    end
endmodule
module file_io_module (
    input  logic clk,
    input  logic wr_en,
    output logic done
);
    integer fd;
    always_ff @(posedge clk) begin
        done <= 0;
        if (wr_en) begin
            fd = $fopen("verilator_file_io_module.tmp", "w");
            if (fd) begin
                $fwrite(fd, "data:%0d\n", 32'hDEADBEEF);
                $fflush(fd);
                $fclose(fd);
                done <= 1;
            end
        end
    end
endmodule
module sys_exec_module (
    input  logic       clk,
    input  logic       exec_en,
    output logic [31:0] status
);
    always_ff @(posedge clk) begin
        if (exec_en) status <= $system("true");
    end
endmodule
module path_test_module (
    input  logic clk,
    input  logic start,
    output logic success
);
    integer fh;
    always_ff @(posedge clk) begin
        success <= 0;
        if (start) begin
            fh = $fopen("../././path_test_module//test.txt", "w");
            if (fh) begin
                $fwrite(fh, "path test\n");
                $fclose(fh);
                success <= 1;
            end
        end
    end
endmodule
module dir_flush_module (
    input  logic clk,
    input  logic create,
    output logic ready
);
    always_ff @(posedge clk) begin
        ready <= 0;
        if (create) begin
            void'($system("mkdir -p verilator_build_dir"));
            ready <= 1;
        end
    end
endmodule
