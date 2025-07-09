class simple_c;
    rand bit [7:0] val;
endclass
module sformatf_mod(input  logic [31:0] in_data,
                    output logic [31:0] out_word);
    always_comb begin
        string s;
        s = $sformatf("VAL=%0d", in_data);
        out_word = in_data;
    end
endmodule
module psprintf_mod(input  logic [7:0] in_byte,
                    output logic [7:0] out_dummy);
    always_comb begin
        string str;
        str = $psprintf("BYTE=%0d", in_byte);
        out_dummy = in_byte;
    end
endmodule
module plusargs_mod(input  logic [7:0] in_sig,
                    output logic       out_flag);
    always_comb begin
        int arg_val;
        out_flag = $value$plusargs("ARG=%d", arg_val);
    end
endmodule
module scope_rand_mod(input  logic [7:0] seed,
                      output logic [7:0] rnd);
    logic [7:0] local_rnd;
    always_comb begin
        int status;
        status = randomize(local_rnd);
        if (status)
            rnd = local_rnd;
        else
            rnd = seed;
    end
endmodule
module class_rand_mod(input  logic clk,
                      output logic [7:0] rand_val);
    always_comb begin
        simple_c obj;
        int ok;
        obj = new();
        ok = obj.randomize();
        if (ok)
            rand_val = obj.val;
        else
            rand_val = 8'd0;
    end
endmodule
module global_clock_mod(input  logic in_bit,
                        output logic out_bit);
    global clocking gclk @(posedge in_bit);
    endclocking
    always @($global_clock) begin
        out_bit <= in_bit;
    end
endmodule
