module deep_parens_mod(input  logic [31:0] in_val,
                       output logic [31:0] out_val);
    assign out_val = (((((((in_val)))))));
endmodule
module fork_mtask_mod(input  logic clk,
                      input  logic rst_n,
                      output logic done);
    task automatic run_parallel;
        fork
            begin
                done <= 1'b1;
            end
        join
    endtask
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            done <= 1'b0;
        end else begin
            run_parallel();
        end
    end
endmodule
module dpi_ucfunc_mod(input  int in_data,
                      output int out_data);
    import "DPI-C" function int  c_func(input int i);
    import "DPI-C" function void c_task(input int i);
    function automatic int compute(input int x);
        compute = c_func(x) + x;
    endfunction
    always_comb begin
        c_task(in_data);
        out_data = compute(in_data);
    end
endmodule
module termop_demo_mod(input  int in_word,
                       output int out_word);
    function automatic int inc_dec(input int v);
        int tmp;
        tmp = v;
        tmp++;
        ++tmp;
        tmp--;
        inc_dec = tmp;
    endfunction
    always_comb begin
        out_word = inc_dec(in_word);
    end
endmodule
