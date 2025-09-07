timeunit 1ns;
timeprecision 1ps;
package CommonTypes;
    typedef struct packed {
        logic [7:0] addr;
        logic [7:0] data;
    } Packet_t;
    typedef Packet_t MyTypedef_t;
endpackage
package MyDPIPackage;
    import "DPI-C" function int dpi_sum_pure (input int a, input int b);
    import "DPI-C" function void dpi_set_data (input int val);
    import "DPI-C" function string dpi_get_string ();
    import "DPI-C" function void dpi_process_vec (input bit [15:0] vec_in, output bit [15:0] vec_out);
    export "DPI-C" task export_task_get_sum;
    task export_task_get_sum (input int a, input int b, output int result);
        result = a + b + 1;
    endtask
    export "DPI-C" function int export_func_mult;
    function int export_func_mult (input int a, input int b);
        return a * b;
    endfunction
endpackage
import CommonTypes::*;
module BasicOpsAndTypes (
    input bit [7:0] in_a,
    input logic [7:0] in_b,
    input real in_r,
    input string in_s,
    output logic [15:0] out_sum,
    output bit out_logic,
    output real out_real,
    output string out_str,
    output logic [3:0] out_bit_sel,
    output logic [7:0] out_concat,
    output logic [2:0] out_repl
);
    timeunit 1ns;
    timeprecision 1ps;
    logic [7:0] local_c;
    bit [7:0] local_d;
    int local_e;
    int signed local_f;
    real local_g;
    string local_h;
    assign local_c = in_a + in_b;
    assign local_d = in_a;
    logic not_c;
    logic red_and_c;
    logic red_or_c;
    assign not_c = ~local_c;
    assign red_and_c = &local_c;
    assign red_or_c = |local_c;
    logic bit_xor_val = in_a ^ in_b;
    logic bit_and_val = in_a & in_b;
    logic bit_or_val = in_a | in_b;
    assign out_sum = in_a + in_b;
    logic [7:0] sub_val = in_a - in_b;
    logic [7:0] mul_val = in_a * in_b;
    logic [7:0] div_val = in_a / in_b;
    logic [7:0] mod_val = in_a % in_b;
    logic [7:0] shl_val = in_a << 1;
    logic [7:0] shr_val = in_b >> 1;
    logic [7:0] ash_val_l = in_a <<< 1;
    logic [7:0] ash_val_r = in_b >>> 1;
    assign out_logic = (in_a == in_b) || (in_r != 1.0);
    bit eq_wildcard;
    assign eq_wildcard = (8'b101? === 8'b101z);
    assign local_e = (in_a > in_b) ? in_a : in_b;
    assign out_real = (in_r == 0.0) ? 1.0 : in_r;
    assign out_bit_sel = in_a[3:0];
    assign out_concat = {in_a[3:0], in_b[3:0]};
    assign out_repl = {3{in_a[0]}};
    assign local_h = in_s;
    assign out_str = {in_s, "suffix"};
    assign local_g = real'(in_a);
endmodule
module StructuredTypes (
    input logic [7:0] in_data,
    input bit in_sel_u,
    output logic [15:0] out_struct_val,
    output logic out_enum_val,
    output MyTypedef_t out_typedef_val
);
    timeunit 1ns;
    timeprecision 1ps;
    typedef enum logic [1:0] {
        STATE_IDLE = 2'b00,
        STATE_RUN = 2'b01,
        STATE_STOP = 2'b10
    } State_t;
    State_t current_state;
    assign out_enum_val = (current_state == STATE_RUN);
    Packet_t pkt_in;
    Packet_t pkt_out;
    typedef union {
        logic [15:0] full_word;
        struct packed {
            logic [7:0] byte_h;
            logic [7:0] byte_l;
        } bytes;
    } Word_u;
    Word_u word_union;
    MyTypedef_t my_packet;
    always_comb begin
        pkt_in.addr = in_data;
        pkt_in.data = ~in_data;
        word_union.full_word = {pkt_in.addr, pkt_in.data};
        if (in_sel_u) begin
            pkt_out.addr = word_union.bytes.byte_h;
            pkt_out.data = word_union.bytes.byte_l;
        end else begin
            pkt_out.addr = word_union.full_word[15:8];
            pkt_out.data = word_union.full_word[7:0];
        end
        out_struct_val = word_union.full_word;
        current_state = STATE_RUN;
        out_typedef_val = pkt_in;
    end
endmodule
module ArraysAndInitializers (
    input logic [3:0] in_idx,
    input logic [7:0] in_val,
    input logic in_push_dyn,
    input logic in_push_queue,
    input logic in_clear_queue,
    output logic [7:0] out_array_val,
    output bit out_dyn_array_empty,
    output int out_queue_size
);
    timeunit 1ns;
    timeprecision 1ps;
    logic [7:0] packed_array [3:0];
    assign packed_array = '{8'h11, 8'h22, 8'h33, 8'h44};
    logic [7:0] unpacked_array [4];
    assign unpacked_array = '{8'hAA, 8'hBB, 8'hCC, 8'hDD};
    assign out_array_val = packed_array[in_idx];
    logic [7:0] assoc_array [string];
    logic [7:0] assoc_val;
    logic [7:0] dyn_array [];
    logic [7:0] dyn_val;
    logic [7:0] data_queue [$];
    logic [7:0] queue_val;
    function automatic bit get_dyn_array_empty(logic [7:0] arr[]);
        return (arr.size() == 0);
    endfunction
    task automatic push_back_dyn_array(ref logic [7:0] arr[], input logic [7:0] val);
        arr = new[arr.size() + 1](arr);
        arr[arr.size() - 1] = val;
    endtask
    function automatic int get_queue_size(logic [7:0] q[$]);
        return q.size();
    endfunction
    task automatic push_front_queue(ref logic [7:0] q[$], input logic [7:0] val);
        q.push_front(val);
    endtask
    task automatic clear_queue(ref logic [7:0] q[$]);
        q.delete();
    endtask
    always_comb begin
        assoc_array["key1"] = 8'hFF;
        if (assoc_array.exists("key1")) begin
            assoc_val = assoc_array["key1"];
        end else begin
            assoc_val = 8'h00;
        end
        if (in_push_dyn) begin
            push_back_dyn_array(dyn_array, in_val);
        end
        if (!get_dyn_array_empty(dyn_array)) begin
            if (dyn_array.size() > 0) begin
                dyn_val = dyn_array[0];
            end
        end
        out_dyn_array_empty = get_dyn_array_empty(dyn_array);
        if (in_push_queue) begin
            push_front_queue(data_queue, in_val);
        end
        if (in_clear_queue) begin
            clear_queue(data_queue);
        end
        out_queue_size = get_queue_size(data_queue);
        if (get_queue_size(data_queue) > 0) begin
            queue_val = data_queue[0];
        end
    end
    logic [15:0] stream_packed;
    logic [7:0] stream_elements [2];
    assign stream_elements = {>>{stream_packed}};
    logic [15:0] stream_unpacked;
    logic [7:0] source_elements [2] = '{8'h55, 8'h66};
    assign stream_unpacked = {<<{source_elements}};
endmodule
module ProceduralFlow (
    input logic clk,
    input logic reset_n,
    input logic enable_comb,
    input logic [1:0] sel_case,
    input bit disable_enable_in,
    output logic [7:0] data_out,
    output logic [7:0] latched_data,
    output logic [7:0] comb_data,
    output logic process_status,
    output logic disable_status
);
    timeunit 1ns;
    timeprecision 1ps;
    logic [7:0] internal_reg;
    logic [7:0] next_internal_reg;
    logic [7:0] current_state_val;
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            internal_reg <= 8'h00;
        end else begin
            internal_reg <= next_internal_reg;
        end
        latched_data <= internal_reg;
    end
    always_comb begin
        if (enable_comb) begin
            next_internal_reg = internal_reg + 1;
        end else begin
            next_internal_reg = internal_reg;
        end
        comb_data = internal_reg;
    end
    always_latch begin
        current_state_val = internal_reg;
    end
    always_comb begin : case_block
        case (sel_case)
            2'b00: data_out = 8'h0A;
            2'b01: data_out = 8'h0B;
            2'b10: data_out = 8'h0C;
            default: data_out = 8'h0F;
        endcase
    end
    logic [3:0] count;
    logic [7:0] sum_val;
    logic dummy_var;
    always_comb begin
        sum_val = 8'h00;
        count = 4'h0;
        while (count < 4'h5) begin
            sum_val = sum_val + 1;
            count = count + 1;
            dummy_var = count;
        end
        process_status = (sum_val == 8'h05);
    end
    logic [7:0] controlled_data;
    always_comb begin : controlled_block
        if (disable_enable_in) begin
            controlled_data = 8'hAA;
        end else begin
            controlled_data = 8'hBB;
        end
    end
    always_ff @(posedge clk) begin : fork_join_block
        fork : my_fork_block
            begin : sub_block_1
                automatic int i = 0;
                i = 1;
            end
            begin : sub_block_2
                automatic int j = 0;
                j = 1;
            end
        join_none
        disable_status <= disable_enable_in;
    end
    always_comb begin
        if (disable_enable_in) begin
            disable controlled_block;
        end
    end
    assign disable_status = disable_enable_in;
endmodule
module FunctionsAndDPI (
    input logic clk,
    input logic reset_n,
    input logic [7:0] func_in,
    input int dpi_int_in,
    input string dpi_string_in,
    input logic [15:0] dpi_vec_in,
    output logic [7:0] func_out,
    output int dpi_int_out,
    output string dpi_string_out,
    output logic [15:0] dpi_vec_out
);
    timeunit 1ns;
    timeprecision 1ps;
    import MyDPIPackage::*;
    function automatic logic [7:0] pure_add (input logic [7:0] a, input logic [7:0] b);
        return a + b;
    endfunction
    task automatic update_func_out (input logic [7:0] val);
        func_out = val;
    endtask
    logic [7:0] current_func_in_val;
    int current_dpi_int_in_val;
    string current_dpi_string_in_val;
    logic [15:0] current_dpi_vec_in_val;
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            func_out <= 8'h00;
            dpi_int_out <= 0;
            dpi_string_out <= "";
            dpi_vec_out <= 16'h0000;
            current_func_in_val <= func_in;
            current_dpi_int_in_val <= dpi_int_in;
            current_dpi_string_in_val <= dpi_string_in;
            current_dpi_vec_in_val <= dpi_vec_in;
        end else begin
            int sum_res;
            string res_str;
            bit [15:0] proc_vec_out;
            sum_res = MyDPIPackage::dpi_sum_pure(current_dpi_int_in_val, 10);
            dpi_int_out <= sum_res;
            MyDPIPackage::dpi_set_data(sum_res);
            res_str = MyDPIPackage::dpi_get_string();
            dpi_string_out <= res_str;
            MyDPIPackage::dpi_process_vec(current_dpi_vec_in_val, proc_vec_out);
            dpi_vec_out <= proc_vec_out;
            update_func_out(pure_add(current_func_in_val, 8'h01));
        end
    end
endmodule
module ClassesAndInterfaces (
    input logic clk,
    input logic [7:0] class_data_in,
    output logic [7:0] class_data_out,
    output logic iface_signal_out
);
    timeunit 1ns;
    timeprecision 1ps;
    class BaseClass;
        rand int value;
        function new();
            value = 0;
        endfunction
        virtual function void set_value(int v);
            value = v;
        endfunction
        constraint value_range { value >= 0; value <= 255; }
    endclass
    class DerivedClass extends BaseClass;
        int offset;
        function new(int o);
            super.new();
            offset = o;
        endfunction
        function void set_value(int v);
            value = v + offset;
        endfunction
    endclass
    interface my_interface (input logic clk);
        logic data;
        logic enable;
        modport MASTER (
            output data,
            input enable
        );
        modport SLAVE (
            input data,
            output enable
        );
        task my_task_if (input logic [7:0] val);
            data = val[0];
        endtask
        function int get_data_if();
            return data;
        endfunction
    endinterface
    always_comb begin
        automatic BaseClass base_obj;
        automatic DerivedClass derived_obj;
        base_obj = new();
        derived_obj = new(10);
        void'(base_obj.randomize());
        base_obj.set_value(class_data_in);
        derived_obj.set_value(class_data_in);
        class_data_out = base_obj.value;
    end
    my_interface iface_inst (.*);
    always_comb begin
        iface_inst.MASTER.data = class_data_in[0];
        iface_inst.SLAVE.enable = iface_inst.MASTER.data;
        iface_signal_out = iface_inst.MASTER.data;
    end
endmodule
module AssertionsAndCoverage (
    input logic clock,
    input logic reset,
    input logic enable_assert,
    input logic [7:0] value_a,
    input logic [7:0] value_b,
    output logic dummy_out_ac
);
    timeunit 1ns;
    timeprecision 1ps;
    always_ff @(posedge clock) begin
        if (enable_assert) begin
            assert property (@(posedge clock) (value_a > value_b));
        end
    end
    covergroup my_covergroup @(posedge clock);
        coverpoint value_a {
            bins zero_to_10 = {[0:10]};
            bins greater_than_zero = {[1:255]};
            ignore_bins big_vals = {[200:255]};
        }
        coverpoint value_b {
            bins low = {0, 1, 2};
            bins high = {253, 254, 255};
        }
        test_cross : cross value_a, value_b;
    endgroup
    my_covergroup cg_inst = new();
    always_ff @(posedge clock) begin
        assume property (@(posedge clock) enable_assert);
    end
    assign dummy_out_ac = (value_a + value_b) > 0;
endmodule
module AttributesAndMisc (
    input logic [7:0] attr_in,
    output logic [7:0] attr_out,
    output logic strength_out
);
    timeunit 1ns;
    timeprecision 1ps;
    (* verilator_opt = "no_warn_LATCH" *) logic [7:0] latched_reg;
    logic internal_wire_val;
    pullup (internal_wire_val);
    assign strength_out = internal_wire_val;
    assign latched_reg = attr_in;
    assign attr_out = latched_reg;
endmodule
program MyProgram (input bit in_val, output bit out_val);
    timeunit 1ns;
    timeprecision 1ps;
    logic internal_prg_var;
    assign internal_prg_var = in_val;
    assign out_val = internal_prg_var;
endprogram
checker MyChecker (input bit clk, input bit data, output bit check_result);
    timeunit 1ns;
    timeprecision 1ps;
    always_ff @(posedge clk) begin
        assert (1'b1);
    end
    assign check_result = data;
endchecker
