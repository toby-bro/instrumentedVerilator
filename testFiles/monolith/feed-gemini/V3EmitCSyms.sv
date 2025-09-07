timeunit 1ns;
timeprecision 1ps;
module mod_basic_hierarchy_vars (
    input bit clk,
    input bit rst_n,
    input logic [7:0] data_in,
    output logic [7:0] data_out
);
    localparam MAX_COUNT = 10;
    logic [3:0] counter_packed;
    logic [7:0] ram_data [0:3];
    int signed_val;
    real floating_point_val;
    string message_str = "Default";
    typedef enum {STATE_IDLE, STATE_ACTIVE, STATE_DONE} fsm_state_e;
    fsm_state_e current_state;
    typedef struct packed {
        logic [1:0] id;
        logic [5:0] value;
    } packet_s;
    packet_s packet_data;
    logic [15:0] public_register;
    logic [7:0] sub_mod_A_out_wire;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            counter_packed <= 0;
            public_register <= 16'hAAAA;
            current_state <= STATE_IDLE;
        end else begin
            if (counter_packed < MAX_COUNT) begin
                counter_packed <= counter_packed + 1;
            end else begin
                counter_packed <= 0;
            end
            public_register <= public_register + data_in;
            case (current_state)
                STATE_IDLE: current_state <= STATE_ACTIVE;
                STATE_ACTIVE: current_state <= STATE_DONE;
                default: current_state <= STATE_IDLE;
            endcase
            ram_data[counter_packed % 4] <= sub_mod_A_out_wire;
        end
    end
    always_comb begin
        logic [7:0] temp_val;
        data_out = ram_data[counter_packed % 4] + data_in;
        signed_val = $signed(data_in) - 50;
        floating_point_val = $itor(data_in) * 2.5;
        packet_data.id = data_in[1:0];
        packet_data.value = data_in[7:2];
        temp_val = data_in;
        if (temp_val == 8'd255) begin
            message_str = "Full";
        end else begin
            message_str = "Not Full";
        end
    end
    sub_mod_A #(
        .WIDTH(8)
    ) i_sub_mod_A (
        .clk(clk),
        .in_val(data_in),
        .out_val(sub_mod_A_out_wire)
    );
endmodule
module sub_mod_A #(parameter WIDTH = 8) (
    input bit clk,
    input logic [WIDTH-1:0] in_val,
    output logic [WIDTH-1:0] out_val
);
    logic [WIDTH-1:0] reg_val;
    always_ff @(posedge clk) begin
        reg_val <= in_val;
    end
    assign out_val = reg_val;
endmodule
package dpi_pkg;
    import "DPI-C" function int dpi_add_int(input int a, input int b);
    import "DPI-C" function real dpi_mul_real(input real x, input real y);
    import "DPI-C" function string dpi_concat_string(input string s1, input string s2);
    import "DPI-C" function void dpi_modify_array(input int num_elements, inout logic [7:0] arr[]);
    export "DPI-C" function dpi_exported_square;
    export "DPI-C" function dpi_exported_log;
    function int dpi_exported_square(input int val);
        return val * val;
    endfunction
    function void dpi_exported_log(input string msg);
    endfunction
endpackage
module mod_dpi_interface (
    input bit clk,
    input int dpi_in_a,
    input real dpi_in_x,
    input string dpi_in_s1,
    input string dpi_in_s2,
    inout logic [7:0] dpi_arr_inout [0:1],
    output int dpi_sum_out,
    output real dpi_prod_out,
    output string dpi_concat_str_out,
    output int dpi_squared_val
);
    import dpi_pkg::dpi_add_int;
    import dpi_pkg::dpi_mul_real;
    import dpi_pkg::dpi_concat_string;
    import dpi_pkg::dpi_modify_array;
    import dpi_pkg::dpi_exported_square;
    import dpi_pkg::dpi_exported_log;
    logic [7:0] local_dpi_arr [0:1];
    assign dpi_arr_inout = local_dpi_arr;
    always_comb begin
        local_dpi_arr = dpi_arr_inout;
        dpi_sum_out = dpi_add_int(dpi_in_a, 5);
        dpi_prod_out = dpi_mul_real(dpi_in_x, 2.0);
        dpi_concat_str_out = dpi_concat_string(dpi_in_s1, dpi_in_s2);
        dpi_modify_array(2, local_dpi_arr);
        dpi_squared_val = dpi_exported_square(dpi_in_a);
        dpi_exported_log("DPI module log message.");
    end
    export "DPI-C" function get_module_id;
    function int get_module_id;
        return 123;
    endfunction
endmodule
module mod_coverage (
    input bit clk,
    input bit rst_n,
    input logic [2:0] state_in,
    input logic [1:0] opcode_in,
    output logic [3:0] out_data
);
    logic [3:0] internal_counter;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            internal_counter <= 0;
        end else begin
            internal_counter <= internal_counter + 1;
        end
    end
    assign out_data = {state_in, opcode_in};
    covergroup cg_fsm_op @(posedge clk);
        option.per_instance = 1;
        option.at_least = 2;
        state_cp : coverpoint state_in {
            bins IDLE = {0};
            bins FETCH = {1};
            bins EXECUTE = {2};
            bins WRITE_BACK = {3};
            bins others = default;
        }
        opcode_cp : coverpoint opcode_in {
            bins ADD = {0};
            bins SUB = {1};
            bins MUL = {2};
            bins DIV = {3};
        }
        state_opcode_cross : cross state_cp, opcode_cp {
            ignore_bins illegal_combo = binsof(state_cp) intersect {0} && binsof(opcode_cp) intersect {3};
        }
    endgroup
    cg_fsm_op i_cg_fsm_op = new();
endmodule
module mod_sv_classes (
    input bit clk,
    input bit reset,
    input int data_payload,
    output int output_data
);
    class MyTransaction;
        rand int id;
        randc int value;
        function new();
            id = 0;
            value = 0;
        endfunction
        function void set_data(int new_id, int new_value);
            this.id = new_id;
            this.value = new_value;
        endfunction
        function int get_sum();
            return id + value;
        endfunction
    endclass
    MyTransaction my_tr_h;
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            if (my_tr_h != null) begin
                my_tr_h = null;
            end
            output_data <= 0;
        end else begin
            if (my_tr_h == null) begin
                my_tr_h = new();
                my_tr_h.set_data(data_payload, data_payload * 2);
            end else begin
                my_tr_h.set_data(data_payload, data_payload * 2);
                void'(my_tr_h.randomize());
            end
            output_data <= my_tr_h.get_sum();
        end
    end
endmodule
module mod_generate_params #(
    parameter NUM_INSTANCES = 2,
    parameter DATA_WIDTH = 4
) (
    input bit clk,
    input logic [DATA_WIDTH-1:0] input_data,
    output logic [DATA_WIDTH-1:0] output_aggregated
);
    logic [DATA_WIDTH-1:0] internal_signals [NUM_INSTANCES-1:0];
    logic [DATA_WIDTH-1:0] sum_accumulator;
    generate
        if (NUM_INSTANCES > 0) begin : gen_non_empty
            localparam EFFECTIVE_WIDTH = DATA_WIDTH;
        end else begin : gen_empty
        end
    endgenerate
    genvar i;
    generate
        for (i = 0; i < NUM_INSTANCES; i = i + 1) begin : gen_sub_modules
            inner_sub_mod #(
                .WIDTH(DATA_WIDTH)
            ) i_inner_sub_mod (
                .clk(clk),
                .in_val(input_data + i),
                .out_val(internal_signals[i])
            );
        end
    endgenerate
    always_comb begin
        sum_accumulator = 0;
        for (int j = 0; j < NUM_INSTANCES; j++) begin
            sum_accumulator = sum_accumulator + internal_signals[j];
        end
        output_aggregated = sum_accumulator;
    end
endmodule
module inner_sub_mod #(parameter WIDTH = 4) (
    input bit clk,
    input logic [WIDTH-1:0] in_val,
    output logic [WIDTH-1:0] out_val
);
    logic [WIDTH-1:0] reg_data;
    always_ff @(posedge clk) begin
        reg_data <= in_val;
    end
    assign out_val = reg_data;
endmodule
interface my_simple_if (input bit clk);
    logic [7:0] data;
    logic req, ack;
    modport MASTER (output data, output req, input ack);
    modport SLAVE (input data, input req, output ack);
    always_ff @(posedge clk) begin
        if (req) begin
            ack <= 1;
        end else begin
            ack <= 0;
        end
    end
endinterface
module mod_scopes_and_vpi (
    input bit clk,
    output logic [7:0] final_result
);
    my_simple_if i_if (.clk(clk));
    mod_using_interface i_mod_if (
        .clk(clk),
        .bus_if(i_if)
    );
    logic [7:0] program_output_dummy;
    program my_program (input bit p_clk, output logic [7:0] p_out);
        logic [7:0] prog_var;
    endprogram
    my_program i_my_program (
        .p_clk(clk),
        .p_out(program_output_dummy)
    );
    assign final_result = i_if.data + program_output_dummy;
endmodule
module mod_using_interface (
    input bit clk,
    my_simple_if bus_if
);
    always_ff @(posedge clk) begin
        bus_if.req <= 1;
        bus_if.data <= 8'hAB;
    end
endmodule
module mod_savable_events (
    input bit clk,
    input bit reset_trigger,
    input int seed_in,
    output int current_random_val
);
    logic [31:0] counter;
    logic [31:0] prev_counter;
    int array_for_save_restore [0:1];
    int regular_int_a;
    int regular_int_b;
    always_ff @(posedge clk) begin
        if (reset_trigger) begin
            counter <= 0;
            prev_counter <= 0;
            array_for_save_restore[0] <= 0;
            array_for_save_restore[1] <= 0;
            regular_int_a <= seed_in;
            regular_int_b <= seed_in * 2;
        end else begin
            prev_counter <= counter;
            counter <= counter + 1;
            array_for_save_restore[0] <= counter;
            array_for_save_restore[1] <= prev_counter;
            regular_int_a <= regular_int_a + 1;
            regular_int_b <= regular_int_b - 1;
            current_random_val <= regular_int_a + regular_int_b;
        end
    end
endmodule
