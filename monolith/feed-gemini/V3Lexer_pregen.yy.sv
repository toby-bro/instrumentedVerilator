module m_basic_types_ops_ids (
    input logic [7:0] in_a,
    input logic [7:0] in_b,
    output logic [15:0] out_result
);
    wire [7:0] w_val; 
    reg [7:0] r_count; 
    integer i_sum; 
    real r_float; 
    time t_delay_val; 
    assign w_val = in_a + in_b; 
    assign out_result = w_val * 2'b11; 
    initial begin 
        i_sum = in_a - in_b; 
        r_float = 3.14159; 
        t_delay_val = 100ns; 
        if (i_sum > 0) begin 
            r_count = i_sum % 8; 
        end else begin 
            r_count = ~i_sum; 
        end 
        case (r_count) 
            0: w_val = in_a & in_b; 
            1: w_val = in_a | in_b; 
            2: w_val = in_a ^ in_b; 
            default: w_val = in_a; 
        endcase 
        r_float = 1.234E+5; 
        r_float = 0.5;
        r_float = 1.0;
        i_sum = 8'o77; 
        i_sum = 16'hFF; 
        logic [7:0] shifted_val = w_val << 2; 
        shifted_val = w_val >> 1; 
        logic is_equal = (in_a == in_b); 
        logic is_not_equal = (in_a != in_b); 
        logic less_than_eq = (in_a <= in_b); 
        logic greater_than_eq = (in_a >= in_b); 
        logic logical_and = (in_a > 0 && in_b > 0); 
        logic logical_or = (in_a < 0 || in_b < 0); 
        logic logical_not = !(in_a == 0); 
        logic xnor_op = in_a ~^ in_b; 
        logic xnor_op2 = in_a ^~ in_b; 
        logic power_op = 2 ** 3; 
        logic implies_op = 1 -> 0; 
        out_result = {in_a, in_b}; 
        out_result = {2{in_a}}; 
        i_sum = $random; 
        t_delay_val = $time; 
    end 
    wire \my variable ; 
    wire \another/escaped-id ;
    /* This is a multi-line
       comment. */ 
endmodule
module m_sv_datatypes_proc_blocks (
    input logic [1:0] sel,
    input bit [3:0] b_in,
    output byte b_out
);
    logic [7:0] l_data; 
    longint li_value; 
    shortint si_value; 
    int i_std_value; 
    string s_message; 
    enum logic {STATE_IDLE, STATE_ACTIVE} current_state; 
    typedef enum logic {STATE_ON, STATE_OFF} my_state_t; 
    struct packed { 
        bit sign;
        logic [7:0] magnitude;
    } s_packed_data;
    union { 
        int i_val;
        real r_val;
    } u_data;
    assign s_message = "SystemVerilog strings"; 
    initial begin
        l_data = b_in;
        b_out = b_in; 
        li_value = 1000000000000000000; 
        si_value = 123;
        i_std_value = $clog2(1024); 
        current_state = STATE_IDLE;
        s_packed_data.sign = 1'b0;
        s_packed_data.magnitude = 8'hFF;
        void'(current_state); 
        localparam int MAX_VAL = 255; 
        automatic int auto_var; 
        static int static_var; 
        const int constant_val = 10; 
        auto_var = 1;
        static_var = 2;
        logic [7:0] signed_data = $signed(l_data); 
        logic [7:0] unsigned_data = $unsigned(l_data); 
    end
    always_ff @(posedge sel[0]) begin 
        b_out++; 
        li_value--; 
        li_value += 10; 
        si_value -= 5; 
        s_packed_data.magnitude *= 2; 
        s_packed_data.magnitude /= 3; 
        s_packed_data.magnitude %= 4; 
        s_packed_data.magnitude &= 5; 
        s_packed_data.magnitude |= 6; 
        s_packed_data.magnitude ^= 7; 
        s_packed_data.magnitude <<= 1; 
        s_packed_data.magnitude >>= 1; 
        l_data = l_data >>> 2; 
        l_data = l_data <<< 2; 
        if (sel === 2'b00) begin 
            l_data = 8'bXXXX; 
        end else if (sel !== 2'b01) begin 
            l_data = 8'bZZZZ; 
        end
        l_data = $bits(b_in); 
        l_data = $countbits(b_in, 1'b1); 
        l_data = $countones(b_in); 
        l_data = $dimensions(b_in); 
        l_data = $left(b_in); 
        l_data = $right(b_in); 
        l_data = $low(b_in); 
        l_data = $high(b_in); 
        l_data = $unit; 
        li_value = $increment; 
        fork 
            int my_local_var = 10;
            my_local_var++;
            break; 
        join_any 
        logic [7:0] temp_data;
        for (int j = 0; j < 8; j++) begin 
            if (j == 4) continue; 
            temp_data[j] = j;
        end
        while (b_out > 0) begin 
            b_out--;
        end
        repeat (2) begin 
            li_value++;
        end
        forever begin 
            break; 
        end
        logic new_var = (new ? 1 : 0); 
        logic this_var = (this ? 1 : 0); 
        logic super_var = (super ? 1 : 0); 
        logic virtual_var = (virtual ? 1 : 0); 
        logic extern_var = (extern ? 1 : 0); 
        logic export_var = (export ? 1 : 0); 
        logic import_var = (import ? 1 : 0); 
    end
endmodule
module m_sv_classes_sva_ops (
    input logic clk,
    input logic reset_n,
    input logic assertion_check_en,
    output logic assert_pass
);
    class MyParentClass; 
        local int parent_data;
    endclass
    class MyClass extends MyParentClass; 
        local int my_private_data; 
        pure virtual function int get_data(); 
        function new(); 
            my_private_data = 0;
            this.my_private_data = 1; 
        endfunction 
        protected int protected_data; 
        constraint c_data {my_private_data inside {[0:100]};}; 
        function void randomize_data(); 
            if (!this.randomize() solve my_private_data before c_data) begin 
                $error("Randomization failed"); 
            end
        endfunction 
        rand int r_val; 
        randc bit [3:0] r_vec; 
    endclass 
    property p_always_high; 
        @(posedge clk) assertion_check_en |-> strong(assert_pass); 
    endproperty 
    sequence s_rising_then_falling; 
        @(posedge clk) reset_n ##1 expect (!reset_n throughout (##[1:5] !reset_n)); 
    endsequence 
    assert property (p_always_high) 
        else $fatal(2, "Assertion failed!"); 
    assume property (p_always_high); 
    cover property (p_always_high); 
    logic [3:0] cp_b_in_var;
    covergroup cg_data @(posedge clk); 
        cp_b_in: coverpoint cp_b_in_var { 
            bins zero = {0}; 
            bins non_zero = default;
            binsof data_range = {0,1,2,3}; 
            ignore_bins ignored = {4}; 
            illegal_bins illegal_val = {5}; 
        }
        cross cp_b_in; 
    endgroup 
    logic s_always_check;
    s_always_check = s_always (reset_n); 
    s_always_check = s_eventually (reset_n); 
    s_always_check = s_nexttime (reset_n); 
    s_always_check = s_until (reset_n, assertion_check_en); 
    s_always_check = s_until_with (reset_n, assertion_check_en); 
    s_always_check = weak(reset_n); 
    s_always_check = until (reset_n, assertion_check_en); 
    s_always_check = until_with (reset_n, assertion_check_en); 
    s_always_check = nexttime (reset_n); 
    s_always_check = eventually (reset_n); 
    s_always_check = untyped(1'b0); 
    checker my_checker (input clk); 
        logic temp_sig;
        assign temp_sig = clk;
    endchecker 
    logic accept_on_sig;
    accept_on_sig = accept_on (posedge clk) (reset_n); 
    accept_on_sig = reject_on (negedge clk) (!reset_n); 
    accept_on_sig = sync_accept_on (posedge clk) (reset_n); 
    accept_on_sig = sync_reject_on (negedge clk) (!reset_n); 
    logic [3:0] val_a, val_b;
    always_comb begin
        case (val_a)
            unique 0: val_b = 0; 
            default: val_b = 1;
        endcase
        case (val_a)
            unique0 0: val_b = 0; 
            default: val_b = 1;
        endcase
        case (val_a)
            priority 0: val_b = 0; 
            default: val_b = 1;
        endcase
        $asserton; 
        $assertoff; 
        $assertctl(1); 
        $assertkill; 
        val_a++; 
        val_a--; 
        val_a += 1; 
        val_a -= 1; 
        val_a *= 1; 
        val_a /= 1; 
        val_a %= 1; 
        val_a &= 1; 
        val_a |= 1; 
        val_a ^= 1; 
        val_a <<= 1; 
        val_a >>= 1; 
        val_a = (val_a === val_b) ? val_a : val_b; 
        val_a = (val_a !== val_b) ? val_a : val_b; 
        val_a = (val_a ~& 1'b1); 
        val_a = (val_a ~| 1'b1); 
        val_a = (val_a ^~ 1'b1); 
        val_a = (val_a ** 2); 
        val_a = 1 -> 2; 
        val_a = 1 ->> 2; 
        val_a = val_b -> assertion_check_en; 
        val_a = val_b <-> assertion_check_en; 
        val_a = val_b :+ 1; 
        val_a = val_b :- 1; 
        val_a = val_b :* val_a; 
        val_a = val_b :: val_a; 
        val_a = val_b := val_a; 
        val_a = val_b :/ val_a; 
        val_a = val_b ||| val_a; 
        val_a = val_b &&& val_a; 
        val_a = val_b |=| val_a; 
        val_a = val_b @* val_a; 
        val_a = val_b <-> val_a; 
        val_a = `VAL; 
        val_a = `(VAL); 
        val_a = val_b |-> val_a; 
        val_a = val_b |=> val_a; 
        val_a = val_b #-# val_a; 
        val_a = val_b #-# val_a; 
        val_a = val_b [-] val_a; 
        val_a = val_b [=] val_a; 
        val_a = val_b [*] val_a; 
        val_a = val_b [+] val_a; 
        val_a = $plusSlashMinus(val_b, val_a); 
        val_a = $plusPctMinus(val_b, val_a); 
    end
endmodule
module m_gate_config_attributes (
    input logic in_data,
    input logic in_enable,
    output logic out_final
);
    wire w_mid;
    and (strong1, weak0) (w_mid, in_data, in_enable); 
    or (pullup, pulldown) (out_final, w_mid, in_enable); 
    not (supply0, supply1) (w_mid, in_data); 
    buf (highz0, highz1) (w_mid, in_data); 
    bufif0 (w_mid, in_data, in_enable); 
    bufif1 (w_mid, in_data, in_enable); 
    cmos (w_mid, in_data, in_enable); 
    nmos (w_mid, in_data, in_enable); 
    pmos (w_mid, in_data, in_enable); 
    rcmos (w_mid, in_data, in_enable); 
    rnmos (w_mid, in_data, in_enable); 
    rpmos (w_mid, in_data, in_enable); 
    tran (w_mid, in_data); 
    tranif0 (w_mid, in_data, in_enable); 
    tranif1 (w_mid, in_data, in_enable); 
    rtran (w_mid, in_data); 
    rtranif0 (w_mid, in_data, in_enable); 
    rtranif1 (w_mid, in_data, in_enable); 
    tri (w_mid); 
    tri0 (w_mid); 
    tri1 (w_mid); 
    triand (w_mid); 
    trior (w_mid); 
    trireg (w_mid); 
    logic config_hit_var;
    assign config_hit_var = (config ? 1 : 0) || (endconfig ? 1 : 0) || (design ? 1 : 0) || (liblist ? 1 : 0) || (instance ? 1 : 0) || (use ? 1 : 0) || (cell ? 1 : 0);
    genvar i_gen; 
    generate 
        if (1) begin
            for (i_gen=0; i_gen<8; i_gen++) begin : gen_loop_name 
                logic temp_gen_reg;
                assign temp_gen_reg = data_in;
            end 
        end
    endgenerate 
    interface my_interface(input logic clk);
        logic data;
        modport master (output data, input clk); 
    endinterface
    clocking cb_block @(posedge clk); 
        default input #1ns output #1ns; 
    endclocking 
    (* keep *) wire my_keep_wire; 
    (* dont_touch = "true" *) wire my_dont_touch_wire; 
    (* verilator_opt = "inline" *) wire my_opt_wire; 
endmodule
module m_ams_pli_misc (
    input logic trigger_in,
    output logic dummy_out
);
    logic [31:0] ams_temp;
    assign dummy_out = trigger_in; 
    always_comb begin
        ams_temp = $1step(trigger_in); 
        ams_temp = $ac_stim; 
        ams_temp = $analysis; 
        ams_temp = $analog; 
        ams_temp = $assert_recompute; 
        ams_temp = $cm_bal; 
        ams_temp = $cm_imp; 
        ams_temp = $cm_op; 
        ams_temp = $connect_module; 
        ams_temp = $connect_recursive; 
        ams_temp = $dc_sweep; 
        ams_temp = $ddt(trigger_in); 
        ams_temp = $delay_mode; 
        ams_temp = $delay_path; 
        ams_temp = $discipline; 
        ams_temp = $domain; 
        ams_temp = $endconnect_module; 
        ams_temp = $enddiscipline; 
        ams_temp = $enddomain; 
        ams_temp = $endfunction_discipline; 
        ams_temp = $endlimits; 
        ams_temp = $endparamset; 
        ams_temp = $endprobetf; 
        ams_temp = $endset_delay_mode; 
        ams_temp = $endsetup_delay; 
        ams_temp = $endspecify_parameters; 
        ams_temp = $endtolerance; 
        ams_temp = $endwreal; 
        ams_temp = $flow; 
        ams_temp = $from; 
        ams_temp = $function_discipline; 
        ams_temp = $gnd; 
        ams_temp = $ground; 
        ams_temp = $large; 
        ams_temp = $limits; 
        ams_temp = $linear; 
        ams_temp = $medium; 
        ams_temp = $noise; 
        ams_temp = $paramset; 
        ams_temp = $parameter_override; 
        ams_temp = $plus; 
        ams_temp = $pm_bal; 
        ams_temp = $pm_imp; 
        ams_temp = $pm_op; 
        ams_temp = $potential; 
        ams_temp = $probe; 
        ams_temp = $probetf; 
        ams_temp = $quantity; 
        ams_temp = $rcross; 
        ams_temp = $rtran; 
        ams_temp = $satby; 
        ams_temp = $set_delay_mode; 
        ams_temp = $setup_delay; 
        ams_temp = $small; 
        ams_temp = $specify_parameters; 
        ams_temp = $static; 
        ams_temp = $struct; 
        ams_temp = $table; 
        ams_temp = $tan; 
        ams_temp = $to; 
        ams_temp = $tolerance; 
        ams_temp = $tr_recompute; 
        ams_temp = $tran_recompute; 
        ams_temp = $transition; 
        ams_temp = $ul_comp; 
        ams_temp = $ul_max; 
        ams_temp = $ul_min; 
        ams_temp = $unknown; 
        ams_temp = $v_comma_comma_comma(trigger_in); 
        ams_temp = $via; 
        ams_temp = $white_noise; 
        ams_temp = $wreal(trigger_in); 
        ams_temp = $z_comma_comma_comma(trigger_in); 
        ams_temp = $zi_comma_comma_comma(trigger_in); 
    end
    logic [31:0] pli_result;
    pli_result = $my_pli_task(trigger_in); 
    string triple_quoted_str = """
        This is a multi-line
        triple-quoted string.
        It can contain "quotes" inside.
        And also newlines.
    """; 
    logic tbl_out_val;
    table 
        0 (01) : (01) : 0 ; 
        1 - : ? : - ; 
        r ? : - : 0 ; 
        f ? : - : 0 ; 
        * * : * : * ; 
        (01x) (01x) : (01x) ; 
        t : ; 
    endtable 
endmodule
