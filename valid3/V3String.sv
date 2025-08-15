module string_escape_example #(parameter int W = 8) (
    input  logic [W-1:0] in_data,
    output logic [W-1:0] out_data
);
    localparam string ESCAPED_STR = "Line1\nLine2\tTabbed\101BellEnd";
    localparam int    STR_LEN_INT = ESCAPED_STR.len();
    localparam logic [W-1:0] STR_LEN_LSB = STR_LEN_INT;
    assign out_data = in_data ^ STR_LEN_LSB;
endmodule
module extremely_long_identifier_name_module_to_trigger_hashed_name_processing_in_verilator_because_the_identifier_is_longer_than_the_default_limit (
    input  logic in_bit,
    output logic out_bit
);
    logic internal_signal_with_an_extremely_and_ridiculously_long_identifier_name_to_trigger_the_hashed_name_path_inside_verilator_processing;
    assign internal_signal_with_an_extremely_and_ridiculously_long_identifier_name_to_trigger_the_hashed_name_path_inside_verilator_processing = in_bit;
    assign out_bit = internal_signal_with_an_extremely_and_ridiculously_long_identifier_name_to_trigger_the_hashed_name_path_inside_verilator_processing;
endmodule
module numeric_underscore_example (
    input  logic [3:0] in_val,
    output logic [3:0] out_val
);
    parameter real PI_APPROX = 3.141_592_653;
    parameter int  HEX_WITH_UNDERSCORES = 32'hdead_beef;
    wire [3:0] temp = in_val ^ HEX_WITH_UNDERSCORES[3:0];
    assign out_val = temp;
endmodule
module casez_wildcard_example (
    input  logic [7:0] opcode,
    output logic       branch
);
    always_comb begin
        branch = 1'b0;
        casez (opcode)
            8'b1??1_??00: branch = 1'b1;
            8'b0??0_??11: branch = 1'b0;
            default: branch = 1'b0;
        endcase
    end
endmodule
module generate_name_depth_example (
    input  logic a,
    output logic z
);
    logic [1:0] inter;
    generate
        genvar i;
        for (i = 0; i < 2; i = i + 1) begin : level_one_generate_block_with_a_reasonably_long_name
            assign inter[i] = a;
        end
    endgenerate
    assign z = &inter;
endmodule
module struct_union_example (
    input  logic sel,
    output logic [7:0] y
);
    typedef struct packed {
        logic [3:0] upper;
        logic [3:0] lower;
    } nibble_s;
    typedef union packed {
        nibble_s n;
        logic [7:0] whole;
    } byte_u;
    byte_u data_u;
    always_comb begin
        if (sel) begin
            data_u.whole = 8'hA5;
        end else begin
            data_u.n.upper = 4'hF;
            data_u.n.lower = 4'h0;
        end
    end
    assign y = data_u.whole;
endmodule
module enum_example (
    input  logic [1:0] state_in,
    output logic [1:0] state_out
);
    typedef enum logic [1:0] {IDLE = 2'b00, RUN = 2'b01, WAIT_ST = 2'b10, DONE = 2'b11} state_e;
    state_e current, next;
    always_comb begin
        current = state_e'(state_in);
        unique case (current)
            IDLE: next = RUN;
            RUN: next = WAIT_ST;
            WAIT_ST: next = DONE;
            default: next = IDLE;
        endcase
    end
    assign state_out = next;
endmodule
module array_of_strings_example (
    input  logic dummy_in,
    output logic [7:0] first_char
);
    localparam string ITEMS [0:2] = '{ "alpha", "beta", "gamma" };
    assign first_char = ITEMS[0][0];
endmodule
module hash_stress_example #(parameter int N = 64) (
    input  logic [N-1:0] bus_in,
    output logic [N-1:0] bus_out
);
    logic [N-1:0] internal_signal_stage_one_with_very_very_long_name_should_be_hashed_properly;
    logic [N-1:0] internal_signal_stage_two_with_very_very_long_name_should_be_hashed_properly;
    assign internal_signal_stage_one_with_very_very_long_name_should_be_hashed_properly = bus_in;
    assign internal_signal_stage_two_with_very_very_long_name_should_be_hashed_properly = internal_signal_stage_one_with_very_very_long_name_should_be_hashed_properly;
    assign bus_out = internal_signal_stage_two_with_very_very_long_name_should_be_hashed_properly;
endmodule
module whitespace_and_identifier_checks (
    input  logic pin,
    output logic pout
);
    localparam string WITH_WHITESPACE = "   multiple\tspaces\n";
    localparam int    COUNT           = WITH_WHITESPACE.len();
    localparam logic  COUNT_LSB       = logic'(COUNT[0]);
    assign pout = pin ^ COUNT_LSB;
endmodule
