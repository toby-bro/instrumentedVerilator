module SvFeatureMod1 (
    input logic clk_i,
    input logic rst_ni,
    input logic [7:0] data_in_i,
    output logic [7:0] data_out_o,
    output logic       status_o
);
    parameter int MAX_VALUE = 100;
    localparam int MIN_VALUE = 10;
    logic [15:0] counter_reg;
    real         analog_value;
    typedef enum {STATE_IDLE, STATE_ACTIVE, STATE_DONE} fsm_state_e;
    fsm_state_e current_state_q;
    fsm_state_e next_state_d;
    typedef struct packed {
        logic [3:0] field_a;
        logic       field_b;
    } my_packed_struct_t;
    my_packed_struct_t packed_data_q;
    class MySvClass;
        rand int class_id;
        logic [7:0] class_data;
        function new(int id_val);
            this.class_id = id_val;
            this.class_data = 8'hAA;
        endfunction
        function automatic void set_data(logic [7:0] new_data);
            this.class_data = new_data;
        endfunction
        function automatic logic [7:0] get_data();
            return this.class_data;
        endfunction
    endclass
    import "DPI-C" function int c_add_one(int val);
    export "DPI-C" function sv_multiply_by_two;
    function automatic int sv_multiply_by_two(int val);
        return val * 2;
    endfunction
    int dpi_input_val;
    int dpi_output_val;
    MySvClass my_object_h;
    logic [7:0] s1_trace_counter_val;
    assign s1_trace_counter_val = counter_reg[7:0];
    initial begin
        my_object_h = new(0);
    end
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            counter_reg <= 16'h0;
            current_state_q <= STATE_IDLE;
            packed_data_q <= '{field_a: 4'h0, field_b: 1'b0};
            data_out_o <= 8'h0;
            status_o <= 1'b0;
            dpi_input_val <= 0;
            dpi_output_val <= 0;
            analog_value <= 0.0;
            if (my_object_h != null) begin
                my_object_h.set_data(8'h0);
            end
        end else begin
            counter_reg <= counter_reg + 1;
            current_state_q <= next_state_d;
            packed_data_q.field_a <= packed_data_q.field_a + 1;
            packed_data_q.field_b <= ~packed_data_q.field_b;
            data_out_o <= data_in_i + 1;
            status_o <= (counter_reg >= MAX_VALUE);
            dpi_input_val <= counter_reg[7:0];
            dpi_output_val <= c_add_one(dpi_input_val);
            if (my_object_h != null) begin
                my_object_h.set_data(counter_reg[7:0]);
                data_out_o <= my_object_h.get_data();
                analog_value <= $itor(my_object_h.class_id);
            end
        end
    end
    always_comb begin
        next_state_d = current_state_q;
        case (current_state_q)
            STATE_IDLE: begin
                if (data_in_i > MIN_VALUE) next_state_d = STATE_ACTIVE;
            end
            STATE_ACTIVE: begin
                if (counter_reg >= MAX_VALUE) next_state_d = STATE_DONE;
            end
            STATE_DONE: begin
                if (data_in_i == 0) next_state_d = STATE_IDLE;
            end
            default: next_state_d = STATE_IDLE;
        endcase
    end
    logic trace_mod_status;
    SvTraceMod trace_instance (
        .clk_i(clk_i),
        .rst_ni(rst_ni),
        .input_val(data_in_i),
        .external_output_val(s1_trace_counter_val),
        .trace_active_o(trace_mod_status)
    );
endmodule
module SvFeatureMod2 (
    input logic clk_i,
    input logic rst_ni,
    input logic [3:0] control_in_i,
    output logic [15:0] result_out_o,
    output logic another_output_o
);
    logic [255:0] wide_data_q;
    int unpacked_array_q[2][4];
    event my_event;
    int savable_int_q;
    logic [31:0] savable_logic_q;
    real savable_real_q;
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            wide_data_q <= 256'h0;
            foreach (unpacked_array_q[i,j]) unpacked_array_q[i][j] <= 0;
            savable_int_q <= 0;
            savable_logic_q <= 0;
            savable_real_q <= 0.0;
            result_out_o <= 16'h0;
        end else begin
            wide_data_q <= wide_data_q + 1;
            unpacked_array_q[0][0] <= unpacked_array_q[0][0] + 1;
            unpacked_array_q[1][3] <= unpacked_array_q[1][3] + 2;
            savable_int_q <= savable_int_q + 1;
            savable_logic_q <= savable_logic_q + 1;
            savable_real_q <= savable_real_q + 0.1;
            result_out_o <= wide_data_q[15:0] + savable_int_q;
            if (savable_int_q % 10 == 0) -> my_event;
        end
    end
    covergroup my_covergroup @(posedge clk_i);
        cp_control_in: coverpoint control_in_i {
            bins zero = (0);
            bins low = ([1:3]);
            bins high = ([4:15]);
        }
        cp_savable_int: coverpoint savable_int_q {
            bins s_low = ([0:10]);
            bins s_mid = ([11:20]);
            bins s_high = default;
        }
        cp_cross: cross cp_control_in, cp_savable_int;
    endgroup
    my_covergroup cg_inst = new();
    always_comb begin
        if (control_in_i == 4'hF) begin
            cover (1'b1);
        end
        if (wide_data_q[0]) begin
            another_output_o = 1'b1;
        end else begin
            another_output_o = 1'b0;
        end
    end
endmodule
module SvTraceMod (
    input logic clk_i,
    input logic rst_ni,
    input logic [7:0] input_val,
    input logic [7:0] external_output_val,
    output logic trace_active_o
);
    logic [3:0] local_counter;
    bit         flag_b;
    integer     int_val;
    longint     long_val;
    real        float_val;
    typedef enum {TRACE_STATE_A, TRACE_STATE_B, TRACE_STATE_C} trace_enum_e;
    trace_enum_e current_trace_state;
    logic [63:0] packed_trace_array;
    logic [127:0] super_wide_data;
    int unpacked_trace_array[5];
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            local_counter <= 4'h0;
            flag_b <= 1'b0;
            int_val <= 0;
            long_val <= 0;
            float_val <= 0.0;
            current_trace_state <= TRACE_STATE_A;
            packed_trace_array <= 64'h0;
            super_wide_data <= 128'h0;
            foreach (unpacked_trace_array[i]) unpacked_trace_array[i] <= 0;
            trace_active_o <= 1'b0;
        end else begin
            local_counter <= local_counter + 1;
            flag_b <= ~flag_b;
            int_val <= int_val + 1;
            long_val <= long_val + 100;
            float_val <= float_val + 0.01;
            packed_trace_array <= packed_trace_array + 1;
            super_wide_data <= super_wide_data + 1;
            unpacked_trace_array[0] <= unpacked_trace_array[0] + 1;
            unpacked_trace_array[4] <= unpacked_trace_array[4] + 10;
            trace_active_o <= (local_counter > 0) || (external_output_val > 0);
            case (local_counter[1:0])
                2'b00: current_trace_state <= TRACE_STATE_A;
                2'b01: current_trace_state <= TRACE_STATE_B;
                2'b10: current_trace_state <= TRACE_STATE_C;
                default: current_trace_state <= TRACE_STATE_A;
            endcase
        end
    end
endmodule
