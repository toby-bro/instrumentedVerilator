primitive my_udp (
    output out_val,
    input a,
    input b
);
    table
      0 0 : 0;
      0 1 : 1;
      1 0 : 1;
      1 1 : 0;
    endtable
endprimitive
package my_test_pkg;
    timeunit 1ns;
    timeprecision 1ps;
    parameter int PKG_PARAM = 5;
    function int pkg_func(int val);
        return val * PKG_PARAM;
    endfunction
endpackage
module mod_basic_features (
    input logic [7:0] in_data,
    input logic clk_in_basic_features,
    output logic [7:0] out_result
);
    timeunit 1ns;
    timeprecision 1ps;
    parameter int PARAM_DEFAULT = 10;
    parameter PARAM_NO_DEFAULT = 0;
    localparam LOCAL_PARAM = 20;
    logic [7:0] static_var_module_scope = 8'hAA;
    logic [7:0] automatic_var_module_scope;
    always_comb begin : named_always_comb
        static logic [7:0] combinational_temp_static = in_data + 1;
        automatic logic [7:0] combinational_temp_auto;
        combinational_temp_auto = combinational_temp_static * 2;
        if (in_data > PARAM_DEFAULT) begin : if_true_block
            out_result = combinational_temp_auto + LOCAL_PARAM;
        end else begin : if_false_block
            out_result = 8'hFF;
        end
    end
    always_ff @(posedge clk_in_basic_features) begin : named_always_ff
        static logic [7:0] sequential_temp_static = 8'h11;
        automatic logic [7:0] sequential_temp_auto;
        sequential_temp_auto = sequential_temp_static + 1;
        static_var_module_scope <= sequential_temp_auto;
    end
    logic [3:0] four_bit_val = '0;
    logic [15:0] sixteen_bit_val = 16'hFFFF;
endmodule
module mod_typedef_types (
    input logic [1:0] selector,
    output logic [7:0] out_value
);
    timeunit 1ns;
    timeprecision 1ps;
    (* public *) typedef enum {
        RED_P,
        GREEN_P = 2,
        BLUE_P = 4
    } public_color_t;
    public_color_t my_public_color = RED_P;
    typedef enum {
        RED,
        GREEN = 2,
        BLUE = 4
    } color_t;
    color_t my_color = RED;
    typedef struct packed {
        logic [3:0] addr;
        logic [3:0] data;
    } packet_t;
    packet_t my_packet;
    enum {
        STATE_IDLE,
        STATE_BUSY
    } current_state;
    struct {
        int x;
        int y;
    } coord_point;
    always_comb begin
        case (selector)
            2'b00: begin
                my_color = RED;
                out_value = 8'd10;
                my_public_color = GREEN_P;
            end
            2'b01: begin
                my_color = GREEN;
                out_value = my_color + my_public_color;
            end
            default: begin
                my_packet.addr = 4'hA;
                my_packet.data = 4'hB;
                out_value = my_packet.addr + my_packet.data;
            end
        endcase
        current_state = STATE_BUSY;
        coord_point.x = 100;
        coord_point.y = 200;
    end
endmodule
module mod_loops (
    input logic [3:0] count_in,
    input logic [7:0] data_array_in [3:0],
    output logic [7:0] sum_out
);
    timeunit 1ns;
    timeprecision 1ps;
    logic [3:0] i;
    logic [7:0] temp_sum;
    static logic [7:0] static_loop_var_with_assign = 8'h00;
    always_comb begin : loop_block
        i = 0;
        temp_sum = 0;
        static_loop_var_with_assign = 8'h10;
        while (i < count_in)
            i++;
        while (i < 8) begin
            i++;
            temp_sum += 1;
        end
        repeat (count_in)
            temp_sum += 1;
        repeat (5) begin
            temp_sum += 2;
            i--;
        end
        do begin
            i++;
            temp_sum += 3;
        end while (i < 10);
        foreach (data_array_in[idx]) begin
            temp_sum += data_array_in[idx];
        end
        sum_out = temp_sum;
    end
endmodule
module mod_functions_tasks_classes (
    input logic [7:0] in_val,
    output logic [7:0] out_val
);
    timeunit 1ns;
    timeprecision 1ps;
    function automatic logic [7:0] my_auto_func (input logic [7:0] arg_in);
        logic [7:0] local_auto_var;
        local_auto_var = arg_in + 1;
        return local_auto_var;
    endfunction
    function static logic [7:0] my_static_func (input logic [7:0] arg_in);
        logic [7:0] local_static_var;
        local_static_var = arg_in + 2;
        return local_static_var;
    endfunction
    import "DPI-C" function int my_dpi_func (input int a, input int b);
    class BaseClass;
        int m_base_data;
        function new();
            m_base_data = 10;
        endfunction
        function int get_base_data();
            return m_base_data;
        endfunction
        function void display_base();
        endfunction
    endclass
    class DerivedClass extends BaseClass;
        int m_derived_data;
        function new();
            super.new();
            m_derived_data = 20;
        endfunction
        function int get_derived_sum();
            return m_base_data + m_derived_data;
        endfunction
    endclass
    DerivedClass derived_obj;
    always_comb begin
        out_val = my_auto_func(in_val) + my_static_func(in_val);
        derived_obj = new();
        if (derived_obj != null) begin
            out_val += derived_obj.get_derived_sum();
        end
    end
endmodule
module mod_attributes (
    input logic [3:0] clk_in,
    output logic [3:0] counter_out
);
    timeunit 1ns;
    timeprecision 1ps;
    (* public *) logic [3:0] public_signal;
    (* clock_enable *) logic [3:0] clock_enable_signal;
    (* forceable *) logic [3:0] forceable_signal;
    (* public_flat *) logic [3:0] public_flat_signal;
    (* public_flat_rd *) logic [3:0] public_flat_rd_signal;
    (* public_flat_rw *) logic [3:0] public_flat_rw_signal;
    (* isolate_assignments *) logic [3:0] isolate_assign_signal;
    (* sformat *) logic [3:0] sformat_signal;
    (* split_var *) logic [3:0] split_var_signal;
    (* sc_bv *) logic [3:0] sc_bv_signal;
    (* clocker *) logic [3:0] clocker_signal;
    (* no_clocker *) logic [3:0] no_clocker_signal;
    (* public_flat_rw *)
    always_ff @(posedge clk_in[0]) begin
        if (public_flat_rw_signal < 10) begin
            public_flat_rw_signal <= public_flat_rw_signal + 1;
        end else begin
            public_flat_rw_signal <= 0;
        end
        counter_out <= public_flat_rw_signal;
        public_signal <= clk_in;
        forceable_signal <= clk_in + 1;
        public_flat_signal <= clk_in + 2;
        public_flat_rd_signal <= clk_in + 3;
        isolate_assign_signal <= clk_in + 4;
        sformat_signal <= clk_in + 5;
        split_var_signal <= clk_in + 6;
        sc_bv_signal <= clk_in + 7;
        clocker_signal <= clk_in + 8;
        no_clocker_signal <= clk_in + 9;
    end
endmodule
module mod_generate_blocks (
    input logic [1:0] sel_gen_if_runtime,
    input logic [1:0] sel_gen_case_runtime,
    output logic [7:0] gen_out,
    output logic [7:0] runtime_case_out
);
    timeunit 1ns;
    timeprecision 1ps;
    parameter int GEN_WIDTH = 8;
    parameter int GEN_IF_PARAM = 1;
    parameter int GEN_CASE_PARAM = 0;
    wire [7:0] generated_output_wire;
    generate
        if (GEN_IF_PARAM == 1) begin : gen_if_mode_1
            logic [GEN_WIDTH-1:0] gen_if_var_1 = 8'hAA;
            assign generated_output_wire = gen_if_var_1;
        end else begin : gen_if_mode_else
            logic [GEN_WIDTH-1:0] gen_if_var_2 = 8'hBB;
            assign generated_output_wire = gen_if_var_2;
        end
    endgenerate
    generate
        case (GEN_CASE_PARAM)
            0: begin : gen_case_00
                assign generated_output_wire = 8'd10;
            end
            1: begin : gen_case_01
                assign generated_output_wire = 8'd20;
            end
            default: begin : gen_case_default
                assign generated_output_wire = 8'd30;
            end
        endcase
    endgenerate
    generate
        if (GEN_IF_PARAM == 2) begin
            logic [7:0] temp_val = 8'd100;
            assign generated_output_wire = temp_val;
        end else begin
            logic [7:0] temp_val = 8'd200;
            assign generated_output_wire = temp_val;
        end
    endgenerate
    generate
        if (GEN_IF_PARAM == 3)
            if (GEN_CASE_PARAM == 0) begin
                logic [7:0] temp_val = 8'd250;
                assign generated_output_wire = temp_val;
            end else begin
                logic [7:0] temp_val = 8'd251;
                assign generated_output_wire = temp_val;
            end
    endgenerate
    assign gen_out = generated_output_wire;
    always_comb begin : runtime_case_logic
        case (sel_gen_if_runtime)
            2'b00: runtime_case_out = 8'd1;
            2'b01: runtime_case_out = 8'd2;
            default: runtime_case_out = 8'd3;
        endcase
    end
endmodule
`timescale 1ns/100ps
module mod_time_functions (
    input logic clk,
    output real current_time_out
);
    timeunit 1ns;
    timeprecision 1ps;
    logic [63:0] time_val_int;
    real time_val_real;
    always_ff @(posedge clk) begin
        time_val_int <= $time;
        time_val_real <= $realtime;
        current_time_out <= time_val_real;
    end
    task my_sformatf_task(input int value_in);
        string formatted_string;
        formatted_string = $sformatf("Value is %0d", value_in);
    endtask
endmodule
module mod_sync_and_imports (
    input logic clk,
    input logic reset_n,
    input logic data_in,
    output logic data_out,
    output logic cb_out_val
);
    timeunit 1ns;
    timeprecision 1ps;
    logic [3:0] counter;
    logic [7:0] gen_out;
    wire sampled_data_in_net;
    logic cb_driven_sig_reg;
    assign sampled_data_in_net = data_in;
    always_ff @(posedge clk or negedge reset_n) begin : clocked_block
        if (!reset_n) begin
            counter <= 4'b0;
            data_out <= 1'b0;
        end else begin
            counter <= counter + 1;
            data_out <= data_in;
        end
    end
    always @(posedge clk) begin : wait_block
        wait(0);
        wait(counter > 2);
    end
    clocking cb @(posedge clk);
        default input #1step;
        default output #0;
        input #2ns sampled_data_in_net;
        output #1ns cb_driven_sig_reg;
    endclocking
    always @(cb) begin
        cb.cb_driven_sig_reg <= cb.sampled_data_in_net;
    end
    assign cb_out_val = cb_driven_sig_reg;
    import my_test_pkg::*;
    parameter int USE_PKG_PARAM = my_test_pkg::PKG_PARAM;
    always_comb begin
        gen_out = my_test_pkg::pkg_func(counter);
    end
endmodule
module mod_constraints (
    input logic trigger,
    output int constrained_val_out
);
    timeunit 1ns;
    timeprecision 1ps;
    class MyConstrainedClass;
        rand int m_val;
        constraint c_range {
            m_val >= 0;
            m_val <= 100;
        }
        constraint c_even {
            m_val % 2 == 0;
        }
        function new();
            m_val = 0;
        endfunction
    endclass
    MyConstrainedClass my_constrained_obj;
    always_comb begin
        my_constrained_obj = new();
        if (trigger) begin
            void'(my_constrained_obj.randomize());
            constrained_val_out = my_constrained_obj.m_val;
        end else begin
            constrained_val_out = 0;
        end
    end
endmodule
module mod_instantiations (
    input logic in_a,
    input logic in_b,
    input logic clk_inst,
    output logic out_c,
    output logic out_d
);
    timeunit 1ns;
    timeprecision 1ps;
    mod_basic_features basic_inst (
        .in_data( {4'b0, in_a, in_b, 2'b0} ),
        .clk_in_basic_features(clk_inst),
        .out_result( out_c )
    );
    logic udp_in_a = in_a;
    logic udp_in_b = in_b;
    my_udp unnamed_udp_inst ( out_d, udp_in_a, udp_in_b );
endmodule
