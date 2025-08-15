class BaseSettings;
    parameter int BASE_PARAM = 10;
    logic [31:0] base_id_val;
    string base_name_str;
    rand int random_gen_val;
    function new(logic [31:0] id, string name);
        this.base_id_val = id;
        this.base_name_str = name;
        void'(this.randomize());
    endfunction
endclass
class DerivedConfig extends BaseSettings;
    parameter logic [7:0] DERIVED_PARAM = 8'hFF;
    bit [63:0] derived_mask_val;
    int unsigned derived_flags_val;
    real temperature_val;
    enum {STATE_IDLE, STATE_ACTIVE, STATE_DONE} current_state_val;
    typedef struct {
        logic [127:0] long_data_val;
        int count_val;
    } unpacked_info_s;
    unpacked_info_s info_struct_inst;
    typedef struct packed {
        bit [1:0] status_bits;
        bit [2:0] code_bits;
    } PackedStatusType;
    PackedStatusType packed_status_inst;
    function new(logic [31:0] id, string name, bit [63:0] mask, int unsigned flags);
        super.new(id, name);
        this.derived_mask_val = mask;
        this.derived_flags_val = flags;
        this.temperature_val = 25.5;
        this.current_state_val = STATE_IDLE;
        this.info_struct_inst.long_data_val = 128'hDEADBEEF_FEDCBA98_76543210_ABCDEF01;
        this.info_struct_inst.count_val = 5;
        this.packed_status_inst = '{status_bits:2'b10, code_bits:3'b101};
    endfunction
endclass
module ClassProcessor(
    input logic [31:0] in_id,
    input string in_name,
    input bit [63:0] in_mask,
    output int unsigned out_flags
);
    DerivedConfig config_inst;
    always_comb begin
        config_inst = new(in_id, in_name, in_mask, 0);
        out_flags = config_inst.derived_flags_val;
    end
endmodule
interface SimpleBusInterface(input bit clk_i);
    logic [7:0] data_signal;
    logic       valid_signal;
    logic       ready_signal;
    modport Producer (
        output data_signal,
        output valid_signal,
        input ready_signal,
        input clk_i
    );
    modport Consumer (
        input data_signal,
        input valid_signal,
        output ready_signal,
        input clk_i
    );
endinterface
module InterfaceHandler(
    input bit i_clk,
    input logic [7:0] i_data_in,
    output logic [7:0] o_data_out
);
    SimpleBusInterface bus_inst_var(.clk_i(i_clk));
    always_comb begin
        bus_inst_var.data_signal = i_data_in;
        bus_inst_var.valid_signal = 1'b1;
        o_data_out = bus_inst_var.data_signal;
    end
endmodule
typedef struct {
    logic [15:0] value_field;
    logic [127:0] wide_data_field;
    int counter_field;
    string name_field;
    bit status_flag_field;
} UnpackedDataType;
typedef union {
    logic [31:0] word_access;
    byte byte_array_access[4];
    real float_access;
} UnpackedMixedType;
module UnpackedTypesHandler(
    input logic [15:0] in_struct_val,
    input int in_struct_count,
    input logic [31:0] in_union_word,
    output logic [15:0] out_struct_val
);
    UnpackedDataType my_unpacked_struct_inst;
    UnpackedMixedType my_unpacked_union_inst;
    always_comb begin
        my_unpacked_struct_inst.value_field = in_struct_val;
        my_unpacked_struct_inst.wide_data_field = 128'h01234567_89ABCDEF_FEDCBA98_76543210;
        my_unpacked_struct_inst.counter_field = in_struct_count;
        my_unpacked_struct_inst.name_field = "SampleUnpackedStruct";
        my_unpacked_struct_inst.status_flag_field = 1'b1;
        my_unpacked_union_inst.word_access = in_union_word;
        out_struct_val = my_unpacked_struct_inst.value_field;
    end
endmodule
typedef struct packed {
    logic [7:0]  byte_vec_field;
    logic [15:0] short_vec_field;
    bit [63:0]   long_vec_field;
} PackedVectorType;
typedef union packed {
    logic [31:0] int_val_field;
    logic [31:0] other_packed_val_field;
} PackedDataOverlapType;
module PackedTypesHandler(
    input logic [7:0] in_packed_byte,
    input logic [31:0] in_packed_int_or_other,
    output logic [7:0] out_packed_byte
);
    PackedVectorType my_packed_struct_local;
    PackedDataOverlapType my_packed_union_local;
    always_comb begin
        my_packed_struct_local.byte_vec_field = in_packed_byte;
        my_packed_struct_local.short_vec_field = 16'hABCD;
        my_packed_struct_local.long_vec_field = 64'hFEDCBA9876543210;
        my_packed_union_local.int_val_field = in_packed_int_or_other;
        out_packed_byte = my_packed_struct_local.byte_vec_field;
    end
endmodule
