module str_len_mod(input string in_str, output int len_out);
    always_comb begin
        len_out = in_str.len();
    end
endmodule
module str_putc_mod(
    input  string in_str,
    input  int    index,
    input  byte   char_in,
    output string out_str
);
    always_comb begin
        automatic string s;
        s = in_str;
        s.putc(index, char_in);
        out_str = s;
    end
endmodule
module str_getc_mod(
    input  string in_str,
    input  int    index,
    output byte   char_out
);
    always_comb begin
        char_out = byte'(in_str.getc(index));
    end
endmodule
module str_to_upper_mod(input string in_str, output string out_str);
    always_comb begin
        out_str = in_str.toupper();
    end
endmodule
module str_to_lower_mod(input string in_str, output string out_str);
    always_comb begin
        out_str = in_str.tolower();
    end
endmodule
module str_compare_mod(
    input  string str_a,
    input  string str_b,
    output int    result
);
    always_comb begin
        result = str_a.compare(str_b);
    end
endmodule
module str_icompare_mod(
    input  string str_a,
    input  string str_b,
    output int    result
);
    always_comb begin
        result = str_a.icompare(str_b);
    end
endmodule
module str_substr_mod(
    input  string in_str,
    input  int    left_idx,
    input  int    right_idx,
    output string out_str
);
    always_comb begin
        out_str = in_str.substr(left_idx, right_idx);
    end
endmodule
module str_atoi_mod(input string in_str, output int result);
    always_comb begin
        result = in_str.atoi();
    end
endmodule
module str_atobin_mod(input string in_str, output int result);
    always_comb begin
        result = in_str.atobin();
    end
endmodule
module str_atooct_mod(input string in_str, output int result);
    always_comb begin
        result = in_str.atooct();
    end
endmodule
module str_atohex_mod(input string in_str, output int result);
    always_comb begin
        result = in_str.atohex();
    end
endmodule
module str_atoreal_mod(input string in_str, output real result);
    always_comb begin
        result = in_str.atoreal();
    end
endmodule
module str_itoa_mod(
    input  int    value_in,
    output string out_str
);
    always_comb begin
        automatic string s;
        s = "";
        s.itoa(value_in);
        out_str = s;
    end
endmodule
module str_hextoa_mod(
    input  int    value_in,
    output string out_str
);
    always_comb begin
        automatic string s;
        s = "";
        s.hextoa(value_in);
        out_str = s;
    end
endmodule
module str_octtoa_mod(
    input  int    value_in,
    output string out_str
);
    always_comb begin
        automatic string s;
        s = "";
        s.octtoa(value_in);
        out_str = s;
    end
endmodule
module str_bintoa_mod(
    input  int    value_in,
    output string out_str
);
    always_comb begin
        automatic string s;
        s = "";
        s.bintoa(value_in);
        out_str = s;
    end
endmodule
module str_realtoa_mod(
    input  real   value_in,
    output string out_str
);
    always_comb begin
        automatic string s;
        s = "";
        s.realtoa(value_in);
        out_str = s;
    end
endmodule
