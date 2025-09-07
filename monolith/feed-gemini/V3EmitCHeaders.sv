module ModuleWithVarsAndParams (
    input logic [7:0] in_data_mvp,
    output logic [15:0] out_result_mvp
);
    logic [3:0] signal_a;
    logic [7:0] signal_b;
    reg [1:0] state_c;
    reg [15:0] counter_d;
    logic [31:0] large_vector_e;
    logic [63:0] super_wide_f;
    logic [7:0] mem_g [0:19];
    logic [15:0] mem_h [0:9];
    logic [0:0] single_bit_i;
    logic [7:0] another_sig_j;
    logic [3:0] one_more_k;
    logic final_output_l;
    logic [99:0] massive_data_block;
    parameter int PARAM_INT_VAL = 123;
    localparam string LOCALPARAM_STR = "VerilatorTest";
    parameter MAX_WIDTH = 64;
    parameter MIN_WIDTH = 1;
    parameter signed_val = -5;
    genvar i_gen;
    generate
        for (i_gen = 0; i_gen < 4; i_gen = i_gen + 1) begin : gen_block
            logic [i_gen:0] gen_var_signal;
            assign gen_var_signal = i_gen;
        end
    endgenerate
    always_comb begin
        signal_a = in_data_mvp[3:0];
        signal_b = in_data_mvp;
        state_c = signal_a[1:0];
        counter_d = {signal_b, signal_a};
        large_vector_e = {counter_d, state_c, signal_b, signal_a};
        super_wide_f = {large_vector_e, large_vector_e[31:0]};
        single_bit_i = large_vector_e[0];
        mem_g[0] = in_data_mvp;
        mem_h[0] = counter_d;
        another_sig_j = mem_g[PARAM_INT_VAL % 20];
        one_more_k = another_sig_j[3:0];
        final_output_l = single_bit_i | one_more_k[0];
        massive_data_block = {super_wide_f, large_vector_e[31:0], large_vector_e[31:0]};
        out_result_mvp = counter_d + PARAM_INT_VAL + signed_val;
    end
endmodule
module ModuleWithEnums (
    input logic [2:0] in_enum_sel_mwe,
    output logic [3:0] out_enum_val_mwe
);
    typedef enum logic [3:0] {
        STATE_IDLE = 4'd0,
        STATE_ACTIVE = 4'd1,
        STATE_PAUSED = 4'd2,
        STATE_STOPPED
    } fsm_state_t;
    typedef enum logic [1:0] {
        RED,
        GREEN = 2'b01,
        BLUE = 2'b10
    } color_t;
    typedef enum logic [7:0] {
        ERROR_NONE = 8'h00,
        ERROR_TIMEOUT = 8'hFF,
        ERROR_UNDEFINED = 8'hZZ
    } error_code_t;
    fsm_state_t current_state;
    color_t current_color;
    error_code_t last_error;
    always_comb begin
        case (in_enum_sel_mwe)
            0: current_state = STATE_IDLE;
            1: current_state = STATE_ACTIVE;
            2: current_state = STATE_PAUSED;
            default: current_state = STATE_STOPPED;
        endcase
        current_color = RED;
        last_error = ERROR_NONE;
        out_enum_val_mwe = current_state;
    end
endmodule
module ModuleWithUnpackedStructs (
    input logic [7:0] in_data_mus,
    output logic out_flag_mus
);
    typedef struct {
        logic [7:0] addr;
        logic [15:0] data;
        logic enable;
    } unpacked_bus_t;
    typedef struct {
        logic [3:0] id;
        rand logic [7:0] value_a;
        logic valid;
        rand int unsigned random_val;
        unpacked_bus_t bus_info;
        logic [3:0] array_unpacked [0:3];
    } my_item_t;
    my_item_t item_instance;
    always_comb begin
        item_instance.bus_info.addr = in_data_mus;
        item_instance.bus_info.data = {in_data_mus, in_data_mus};
        item_instance.bus_info.enable = in_data_mus[0];
        item_instance.id = in_data_mus[3:0];
        item_instance.value_a = in_data_mus;
        item_instance.valid = in_data_mus[7];
        item_instance.random_val = 0;
        item_instance.bus_info.addr = in_data_mus + 1;
        item_instance.bus_info.data = {in_data_mus, in_data_mus} + 2;
        item_instance.bus_info.enable = in_data_mus[1];
        item_instance.array_unpacked[0] = in_data_mus[3:0];
        item_instance.array_unpacked[1] = in_data_mus[7:4];
        out_flag_mus = item_instance.valid && item_instance.bus_info.enable;
    end
endmodule
module ModuleWithPackedStructsAndUnions (
    input logic [63:0] in_packed_data_mpsu,
    output logic [7:0] out_packed_field_mpsu
);
    typedef struct packed {
        logic [7:0] header;
        logic [15:0] payload;
        logic [7:0] checksum;
    } packet_t;
    typedef struct packed {
        logic [3:0] cmd;
        logic [1:0] status;
        packet_t inner_packet;
        logic [63:0] very_wide_field;
        logic [0:1][7:0] array_field;
    } complex_packed_t;
    typedef union packed {
        logic [31:0] full_word;
        struct packed {
            logic [15:0] lower_half;
            logic [15:0] upper_half;
        } halves;
        struct packed {
            logic [7:0] byte0;
            logic [7:0] byte1;
            logic [7:0] byte2;
            logic [7:0] byte3;
        } bytes;
    } packed_word_t;
    complex_packed_t my_complex_packed;
    packed_word_t my_packed_word;
    always_comb begin
        my_complex_packed.cmd = in_packed_data_mpsu[3:0];
        my_complex_packed.status = in_packed_data_mpsu[5:4];
        my_complex_packed.inner_packet.header = in_packed_data_mpsu[13:6];
        my_complex_packed.inner_packet.payload = in_packed_data_mpsu[29:14];
        my_complex_packed.inner_packet.checksum = in_packed_data_mpsu[37:30];
        my_complex_packed.very_wide_field = in_packed_data_mpsu;
        my_complex_packed.array_field[0] = in_packed_data_mpsu[7:0];
        my_complex_packed.array_field[1] = in_packed_data_mpsu[15:8];
        my_packed_word.full_word = in_packed_data_mpsu[31:0];
        my_packed_word.halves.lower_half = in_packed_data_mpsu[15:0];
        my_packed_word.bytes.byte0 = in_packed_data_mpsu[7:0];
        out_packed_field_mpsu = my_complex_packed.inner_packet.header;
    end
endmodule
module ModuleWithFunctionsAndDPI (
    input logic [7:0] in_val_mfad,
    output logic [7:0] out_val_mfad
);
    import "DPI-C" function int sv_add_one(input int a);
    export "DPI-C" function sv_multiply_by_two;
    function int sv_multiply_by_two(input int a);
        return a * 2;
    endfunction
    function automatic logic [7:0] my_sv_function(input logic [7:0] arg1, input logic [7:0] arg2);
        return (arg1 + arg2);
    endfunction
    task my_sv_task(input logic [7:0] task_in, output logic [7:0] task_out);
        task_out = my_sv_function(task_in, 8'd5);
    endtask
    logic [7:0] func_result;
    logic [7:0] task_result;
    always_comb begin
        func_result = my_sv_function(in_val_mfad, 8'd10);
        out_val_mfad = sv_add_one(func_result);
        my_sv_task(in_val_mfad, task_result);
    end
endmodule
module SubModule (
    input logic [3:0] in_sub,
    output logic [7:0] out_sub
);
    assign out_sub = in_sub * 3;
endmodule
module HierarchicalModule (
    input logic [3:0] in_h,
    output logic [7:0] out_h
);
    logic [3:0] internal_sig;
    logic [7:0] sub_out;
    SubModule sub_inst (
        .in_sub(in_h),
        .out_sub(sub_out)
    );
    assign internal_sig = in_h * 2;
    assign out_h = sub_out + internal_sig;
endmodule
class BaseClass;
    rand int base_val;
    function new();
        base_val = 10;
    endfunction
    virtual function int get_value();
        return base_val;
    endfunction
endclass
class MyComplexClass extends BaseClass;
    rand int complex_id;
    rand bit [7:0] complex_data;
    int internal_state;
    constraint c_complex_id { complex_id > 0; complex_id < 100; }
    constraint c_complex_data { complex_data inside {[10:50]}; }
    function new();
        super.new();
        complex_id = 1;
        complex_data = 8'd10;
        internal_state = 5;
    endfunction
    function void set_state(int new_state);
        internal_state = new_state;
    endfunction
    virtual function int get_value();
        return super.get_value() + internal_state;
    endfunction
    function int get_loose_method_value();
        return complex_id * 2;
    endfunction
endclass
module ClassHost (
    input logic [7:0] in_class_val,
    output logic [15:0] out_class_result
);
    MyComplexClass class_inst_handle;
    logic [7:0] current_internal_state;
    logic [15:0] current_combined_value;
    always_comb begin
        if (class_inst_handle == null) begin
            class_inst_handle = new();
            class_inst_handle.base_val = 20;
            class_inst_handle.complex_id = 30;
            class_inst_handle.complex_data = in_class_val;
        end
        class_inst_handle.set_state(in_class_val[3:0]);
        current_internal_state = class_inst_handle.internal_state;
        current_combined_value = class_inst_handle.get_value() + class_inst_handle.complex_id;
        out_class_result = current_combined_value + current_internal_state;
    end
endmodule
