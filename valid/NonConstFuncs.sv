module mod_ferror(
    input  logic [31:0] fd_in,
    output logic [31:0] err_out
);
    string err_msg;
    always_comb begin
        err_out = $ferror(fd_in, err_msg);
    end
endmodule
module mod_fgets(
    input  logic [31:0] fd_in,
    output logic [31:0] count_out
);
    string line_buf;
    always_comb begin
        count_out = $fgets(line_buf, fd_in);
    end
endmodule
module mod_fscanf(
    input  logic [31:0] fd_in,
    output logic [31:0] status_out
);
    int value_scanned;
    always_comb begin
        status_out = $fscanf(fd_in, "%d", value_scanned);
    end
endmodule
module mod_sscanf(
    input  logic dummy_in,
    output logic [31:0] status_out
);
    int value_scanned;
    string local_str;
    always_comb begin
        local_str  = "123";
        status_out = $sscanf(local_str, "%d", value_scanned);
    end
endmodule
module mod_fread(
    input  logic [31:0] fd_in,
    output logic [31:0] count_out
);
    int data_buf;
    always_comb begin
        count_out = $fread(data_buf, fd_in);
    end
endmodule
module mod_dist_uniform(
    input  logic [31:0] high_in,
    output logic [31:0] rand_out
);
    int result_var;
    always_comb begin
        rand_out = $dist_uniform(result_var, 0, high_in);
    end
endmodule
module mod_dist_normal(
    input  logic [31:0] sigma_in,
    output logic [31:0] rand_out
);
    int result_var;
    always_comb begin
        rand_out = $dist_normal(result_var, 0, sigma_in);
    end
endmodule
module mod_dist_exponential(
    input  logic [31:0] lambda_in,
    output logic [31:0] rand_out
);
    int result_var;
    always_comb begin
        rand_out = $dist_exponential(result_var, lambda_in);
    end
endmodule
module mod_dist_poisson(
    input  logic [31:0] mean_in,
    output logic [31:0] rand_out
);
    int result_var;
    always_comb begin
        rand_out = $dist_poisson(result_var, mean_in);
    end
endmodule
module mod_dist_chi_square(
    input  logic [31:0] k_in,
    output logic [31:0] rand_out
);
    int result_var;
    always_comb begin
        rand_out = $dist_chi_square(result_var, k_in);
    end
endmodule
module mod_dist_t(
    input  logic [31:0] df_in,
    output logic [31:0] rand_out
);
    int result_var;
    always_comb begin
        rand_out = $dist_t(result_var, df_in);
    end
endmodule
module mod_dist_erlang(
    input  logic [31:0] k_in,
    output logic [31:0] rand_out
);
    int result_var;
    always_comb begin
        rand_out = $dist_erlang(result_var, k_in, 1);
    end
endmodule
module mod_sampled(
    input  logic        clk,
    input  logic        sig_in,
    output logic        sampled_out
);
    always_ff @(posedge clk) begin
        sampled_out <= $sampled(sig_in);
    end
endmodule
module mod_past(
    input  logic        clk,
    input  logic        sig_in,
    output logic        past_out
);
    always_ff @(posedge clk) begin
        past_out <= $past(sig_in, 1);
    end
endmodule
module mod_countdrivers(
    input  logic unused_in,
    output logic bit_out
);
    wire net_sig;
    int drv1;
    int drv2;
    always_comb begin
        bit_out = $countdrivers(net_sig, drv1, drv2);
    end
endmodule
module mod_getpattern(
    input  logic [15:0] data_in,
    output logic [15:0] pattern_out
);
    assign pattern_out = $getpattern(data_in);
endmodule
module mod_stacktrace(
    input  logic dummy_in,
    output logic flag_out
);
    string trace_str;
    always_comb begin
        trace_str = $stacktrace();
        flag_out  = 1'b0;
    end
endmodule
module mod_testplusargs(
    input  logic dummy_in,
    output logic flag_out
);
    assign flag_out = $test$plusargs("TEST");
endmodule
