typedef struct {
    bit  [7:0]  a;
    bit [15:0]  b;
} unpacked_struct_t;
class Packet;
    int id;
endclass
module fmt_integral(
    input  logic [15:0] in_val,
    output logic [15:0] out_val
);
    string msg;
    always_comb begin
        msg = $sformatf("d=%0d h=%0h b=%0b o=%0o c=%c",
                        in_val, in_val, in_val, in_val, 8'd65);
        out_val = in_val;
    end
endmodule
module fmt_float(
    input  real in_real,
    output logic valid
);
    string fmt;
    always_comb begin
        fmt   = $sformatf("e:%e f:%f g:%g", in_real, in_real, in_real);
        valid = (in_real != 0.0);
    end
endmodule
module fmt_strength(
    input  logic in_bit,
    output logic out_bit
);
    string msg;
    always_comb begin
        msg     = $sformatf("strength:%v", in_bit);
        out_bit = in_bit;
    end
endmodule
module fmt_raw(
    input  logic [31:0] data_in,
    output logic        flag_out
);
    unpacked_struct_t us;
    string raw_u, raw_z;
    always_comb begin
        us.a = data_in[7:0];
        us.b = data_in[23:8];
        raw_u = $sformatf("%u", us);
        raw_z = $sformatf("%z", us);
        flag_out = us.a[0];
    end
endmodule
module fmt_special_pointer(
    input  logic       enable,
    output logic [3:0] id_out
);
    Packet p;
    string s_hier, s_ptr;
    always_comb begin
        if (p == null)
            p = new();
        p.id   = 9;
        s_hier = $sformatf("hier=%m");
        s_ptr  = $sformatf("ptr=%p", p);
        id_out = enable ? p.id[3:0] : 4'd0;
    end
endmodule
module fmt_time(
    input  logic trigger,
    output logic out_flag
);
    string time_msg;
    time   t_now;
    always_comb begin
        t_now    = $time;
        time_msg = $sformatf("time=%t", t_now);
        out_flag = trigger;
    end
endmodule
