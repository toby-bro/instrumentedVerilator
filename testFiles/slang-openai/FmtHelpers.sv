module fmt_ints(input  logic [31:0] in_val,
                output logic [31:0] out_val);
    string fmt_res;
    always_comb begin
        fmt_res = $sformatf("INTs d=%0d h=%0h x=%0x o=%0o b=%0b c=%c s=%s",
                            in_val, in_val, in_val, in_val, in_val, 8'd65, "hello");
        out_val = in_val;
    end
endmodule
module fmt_float(input  real  in_real,
                 output real  out_real);
    string fmt_res;
    always_comb begin
        fmt_res = $sformatf("FLOAT f=%f e=%e g=%g t=%t",
                            in_real, in_real, in_real, 32'd123);
        out_real = in_real;
    end
endmodule
module fmt_strength(input  logic [3:0] vec_in,
                    output logic [3:0] vec_out);
    string fmt_res;
    always_comb begin
        fmt_res = $sformatf("Vector strength=%v", vec_in);
        vec_out = vec_in;
    end
endmodule
module fmt_raw(input  logic [7:0] a_in,
               input  logic [7:0] b_in,
               output logic [7:0] y_out);
    typedef struct {
        logic [7:0] a;
        logic [7:0] b;
    } s_t;
    s_t s;
    string fmt_res;
    always_comb begin
        s = '{a:a_in, b:b_in};
        fmt_res = $sformatf("RAW U=%u Z=%z", s, s);
        y_out = a_in ^ b_in;
    end
endmodule
module fmt_ptr(input  logic [31:0] p_in,
               output logic [31:0] p_out);
    string fmt_res;
    always_comb begin
        fmt_res = $sformatf("Pointer=%p", p_in);
        p_out   = ~p_in;
    end
endmodule
module fmt_scope_info(input  logic sig_in,
                      output logic sig_out);
    string fmt_res;
    always_comb begin
        fmt_res = $sformatf("Scope=%m Level=%l");
        sig_out = sig_in;
    end
endmodule
