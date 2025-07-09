module time_funcs (
    input  logic clk,
    output logic [63:0] current_time
);
    always_comb begin
        current_time = $time + $stime + $realtime;
    end
endmodule
module random_funcs (
    input  logic [31:0] seed_in,
    output logic [31:0] random_val
);
    logic [31:0] tmp1, tmp2, tmp3;
    always_comb begin
        tmp1       = $random(seed_in);
        tmp2       = $urandom(seed_in);
        tmp3       = $urandom_range(0, 255);
        random_val = tmp1 ^ tmp2 ^ tmp3;
    end
endmodule
module file_io_funcs (
    input  logic trigger,
    output logic [31:0] status_out
);
    integer fd;
    string  line;
    string  errstr;
    integer tmp;
    byte unsigned buffer[0:15];
    always_comb begin
        fd  = $fopen("dummy.txt", "r");
        tmp = $fgetc(fd);
        tmp = $ungetc(8'd65, fd);
        tmp = $ftell(fd);
        tmp = $fseek(fd, 0, 0);
        $rewind(fd);
        $fflush(fd);
        tmp = $feof(fd);
        tmp = $ferror(fd, errstr);
        tmp = $fgets(line, fd);
        tmp = $fread(buffer, fd);
        tmp = $fscanf(fd, "%d", status_out);
        tmp = $sscanf("42", "%d", status_out);
        $fclose(fd);
        status_out = tmp;
    end
endmodule
module distribution_funcs (
    input  logic [31:0] seed_in,
    output logic [31:0] dist_out
);
    int rand_seed;
    int d1, d2, d3, d4, d5, d6, d7;
    always_comb begin
        rand_seed = seed_in;
        d1 = $dist_uniform(rand_seed, 0, 10);
        d2 = $dist_normal(rand_seed, 0, 10);
        d3 = $dist_exponential(rand_seed, 5);
        d4 = $dist_poisson(rand_seed, 3);
        d5 = $dist_chi_square(rand_seed, 2);
        d6 = $dist_t(rand_seed, 1);
        d7 = $dist_erlang(rand_seed, 3, 2);
        dist_out = d1 ^ d2 ^ d3 ^ d4 ^ d5 ^ d6 ^ d7;
    end
endmodule
module countdrivers_func (
    input  wire in_sig,
    output logic result
);
    wire net_sig;
    assign net_sig = in_sig;
    logic drivers;
    always_comb begin
        drivers = $countdrivers(net_sig);
        result  = drivers;
    end
endmodule
module getpattern_func (
    input  logic [7:0] in_data,
    output logic [7:0] pattern
);
    always_comb begin
        pattern = $getpattern(in_data);
    end
endmodule
module plusargs_func (
    input  logic dummy,
    output logic found
);
    always_comb begin
        found = $test$plusargs("TEST_ARG");
    end
endmodule
module property_funcs (
    input  logic clk,
    input  logic sig,
    output logic out_sig
);
    always_ff @(posedge clk) begin
        out_sig <= $rose(sig) ^ $fell(sig) ^ $changed(sig) ^ $stable(sig) ^ $past(sig) ^ $sampled(sig);
    end
endmodule
