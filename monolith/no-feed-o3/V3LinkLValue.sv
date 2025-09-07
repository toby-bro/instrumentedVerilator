module simple_out(input  logic i, output logic o);
    assign o = i;
endmodule
module link_child(input logic in, output logic out);
    assign out = in;
endmodule
module assign_strength_m(input  wire a, output wire b);
    assign (strong1, weak0) b = a;
endmodule
module pin_instance_m(input logic d, output logic e);
    link_child u0 (.in(d), .out(e));
endmodule
module initial_static_m(input  logic [7:0] in_val, output logic [7:0] out_val);
    function automatic logic [7:0] incr(input logic [7:0] a);
        incr = a + 1;
    endfunction
    static logic [7:0] static_var = incr(in_val);
    assign out_val = static_var;
endmodule
module force_release_m(input logic clk, input logic sig_in, output logic sig_out);
    always_ff @(posedge clk) sig_out <= sig_in;
    initial begin
        force sig_out = 1'b1;
        release sig_out;
    end
endmodule
module fire_event_m(input logic trigger, output logic dummy);
    event ev;
    always_comb begin
        if (trigger) -> ev;
        dummy = trigger;
    end
endmodule
module cast_dynamic_m(input logic [3:0] in_bus, output logic [3:0] out_bus);
    always_comb begin
        int success;
        success = $cast(out_bus, in_bus);
    end
endmodule
module file_ops_m(input logic in_sig, output logic out_sig);
    integer fd;
    string  str;
    always_comb begin
        int rv;
        fd  = 32'h0;
        rv  = $ferror(fd, str);
        rv  = $fgets(str, fd);
        rv  = $fread(fd, str);
        rv  = $fscanf(fd, "%s", str);
        rv  = $fungetc(fd, 8'h41);
        rv  = $sscanf("abc", "%s", str);
        out_sig = in_sig;
    end
endmodule
module readmem_m(input logic [7:0] din, output logic [7:0] dout);
    logic [7:0] mem [0:15];
    initial $readmemh("memory.hex", mem);
    assign dout = din;
endmodule
module random_m(input logic clk, input logic [31:0] seed_in, output logic [31:0] rand_out);
    always_ff @(posedge clk) rand_out <= $random(seed_in);
endmodule
module plusargs_m(input logic dummy_in, output logic flag);
    integer val;
    always_comb begin
        flag = $test$plusargs("enable") ? 1'b1 : 1'b0;
        if ($value$plusargs("value=%d", val)) flag = val[0];
    end
endmodule
module sformat_m(input logic [31:0] val_in, output logic [31:0] val_out);
    string s;
    always_comb begin
        $sformat(s, "Value=%0d", val_in);
        val_out = val_in;
    end
endmodule
module incdec_m(input logic [3:0] a_in, output logic [3:0] b_out);
    logic [3:0] tmp;
    always_comb begin
        tmp = a_in;
        ++tmp;
        tmp--;
        b_out = tmp;
    end
endmodule
module select_m(input logic [7:0] in_bus, output logic bit0);
    assign bit0 = in_bus[0];
endmodule
module struct_m(input logic [3:0] in_bus, output logic [3:0] out_bus);
    typedef struct packed { logic [3:0] field; } my_s;
    my_s s;
    always_comb begin
        s.field = in_bus;
        out_bus = s.field;
    end
endmodule
module cell_array_m(input logic in_sig, input logic sel, output logic out_sig);
    logic i_route [0:1];
    logic o_route [0:1];
    simple_out cells0 (.i(i_route[0]), .o(o_route[0]));
    simple_out cells1 (.i(i_route[1]), .o(o_route[1]));
    assign i_route[0] = in_sig;
    assign i_route[1] = in_sig;
    assign out_sig   = (sel) ? cells1.o : cells0.o;
endmodule
module constraint_m(input logic trig, output logic [7:0] rnd_val);
    class rand_class;
        rand bit [7:0] value;
        constraint c1 { value inside {[8'd0:8'd100]}; }
        constraint c2 { value dist { [8'd0:8'd10] :/ 2, 8'd20 := 1}; }
    endclass
    rand_class rc;
    logic [7:0] rnd_reg;
    assign rnd_val = rnd_reg;
    initial begin
        rc = new();
        void'(rc.randomize());
        rnd_reg = rc.value;
        void'(trig);  
    end
endmodule
module task_call_m(input logic a, output logic b);
    task automatic t1(output logic o, input logic i);
        o = i;
    endtask
    always_comb begin
        t1(b, a);
    end
endmodule
