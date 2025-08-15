module ParamModule1 #(
    parameter int DATA_WIDTH = 8,
    parameter real THRESHOLD_VAL = 3.14,
    parameter string MESSAGE = "Hello",
    parameter int ARRAY_SIZE = 4
) (
    input logic [DATA_WIDTH-1:0] in_data,
    output logic [DATA_WIDTH-1:0] out_data
);
    localparam int HALF_WIDTH = DATA_WIDTH / 2;
    logic [HALF_WIDTH-1:0] internal_reg;
    logic [DATA_WIDTH-1:0] data_array [ARRAY_SIZE-1:0];
    always_comb begin
        if (in_data > THRESHOLD_VAL) begin
            out_data = in_data + 1;
        end else begin
            out_data = in_data - 1;
        end
        internal_reg = in_data[HALF_WIDTH-1:0];
        for (int i=0; i<ARRAY_SIZE; i++) begin
            data_array[i] = in_data + i;
        end
    end
endmodule
interface AxiStream_if #(
    parameter int AXIS_DATA_WIDTH = 32
) (
    input logic clk,
    input logic rst_n
);
    logic [AXIS_DATA_WIDTH-1:0] tdata;
    logic tvalid;
    logic tready;
    modport MASTER (
        output tdata, tvalid,
        input tready, clk, rst_n
    );
    modport SLAVE (
        input tdata, tvalid,
        output tready, clk, rst_n
    );
endinterface
module InterfaceWrapper #(
    parameter int CONFIG_ID = 0
) (
    input logic clk_i,
    input logic rst_n_i,
    input logic [CONFIG_ID+7:0] data_in,
    output logic [(CONFIG_ID+7)*2-1:0] data_out
);
    AxiStream_if #( .AXIS_DATA_WIDTH(32) ) axi_master_inst ( .clk(clk_i), .rst_n(rst_n_i) );
    AxiStream_if #( .AXIS_DATA_WIDTH(64) ) axi_slave_inst ( .clk(clk_i), .rst_n(rst_n_i) );
    assign axi_master_inst.tdata = { {32-CONFIG_ID-8{1'b0}}, data_in };
    assign axi_master_inst.tvalid = 1'b1;
    assign axi_slave_inst.tready = axi_master_inst.tvalid;
    always_comb begin
        data_out = {axi_slave_inst.tdata, axi_master_inst.tdata};
    end
endmodule
class MyParameterizedClass #(
    parameter type T = int,
    parameter int MAX_DEPTH = 8
);
    T internal_value;
    T data_store [MAX_DEPTH-1:0];
    function new(T initial_val);
        internal_value = initial_val;
        for (int i=0; i<MAX_DEPTH; i++) begin
            data_store[i] = initial_val + i;
        end
    endfunction
    function T get_value();
        return internal_value;
    endfunction
    function void set_value(T new_val);
        internal_value = new_val;
    endfunction
endclass
module ClassUser (
    input logic [7:0] in_val,
    output logic [15:0] out_val
);
    logic dummy_trigger; 
    always_comb begin : class_inst_block
        MyParameterizedClass #( .T(logic [15:0]), .MAX_DEPTH(10) ) class_inst1;
        MyParameterizedClass #( .T(real), .MAX_DEPTH(5) ) class_inst2;
        logic [15:0] val1;
        real val2;
        class_inst1 = new(16'hAAAA);
        class_inst2 = new(3.14159);
        val1 = class_inst1.get_value();
        class_inst1.set_value(val1 + in_val);
        val2 = class_inst2.get_value();
        class_inst2.set_value(val2 * 2.0);
        out_val = class_inst1.internal_value;
    end
    assign dummy_trigger = in_val[0]; 
endmodule
module GenerateModule_CorrectedOutputs #(
    parameter int SELECT_MODE = 0,
    parameter int NUM_BLOCKS = 2,
    parameter int START_VAL = 1
) (
    input logic [7:0] data_in,
    output logic [7:0] data_out
);
    logic [7:0] internal_data;
    logic [7:0] generated_data_out;
    generate
        if (SELECT_MODE == 0) begin : gen_if_block_0
            assign internal_data = data_in + 1;
        end else if (SELECT_MODE == 1) begin : gen_if_block_1
            assign internal_data = data_in * 2;
        end else begin : gen_if_block_default
            assign internal_data = data_in;
        end
    endgenerate
    genvar k;
    generate
        if (NUM_BLOCKS > 0) begin : gen_for_active
            for (k = START_VAL; k < NUM_BLOCKS + START_VAL; k++) begin : gen_for_blocks
                localparam int BLOCK_OFFSET = k * 2;
                logic [7:0] block_result;
                case (k)
                    0: begin : case_0_assign
                        assign block_result = internal_data + 10;
                    end
                    1: begin : case_1_assign
                        assign block_result = internal_data - 5;
                    end
                    default: begin : case_default_assign
                        assign block_result = internal_data + BLOCK_OFFSET;
                    end
                endcase
                if (k == NUM_BLOCKS + START_VAL - 1) begin : final_block_assign
                    assign generated_data_out = block_result;
                end
            end
        end else begin : gen_for_inactive
            assign generated_data_out = internal_data;
        end
    endgenerate
    assign data_out = generated_data_out;
endmodule
module HierBlockParamModule #(
    parameter int BASE_ADDR = 16'h1000,
    parameter int REG_COUNT = 4,
    parameter type CUSTOM_TYPE = logic [3:0],
    parameter string BLOCK_NAME = "DEFAULT",
    parameter real DELAY_FACTOR = 1.0
) (
    input logic [15:0] addr_in,
    input CUSTOM_TYPE write_data_in,
    output CUSTOM_TYPE read_data_out
);
    localparam int TOTAL_SIZE = REG_COUNT * $bits(CUSTOM_TYPE);
    CUSTOM_TYPE registers[REG_COUNT];
    localparam string MSG = BLOCK_NAME;
    logic [15:0] internal_addr;
    assign internal_addr = addr_in + (DELAY_FACTOR > 0.5 ? 10 : 0);
    always_comb begin
        for (int i=0; i<REG_COUNT; i++) begin
            registers[i] = CUSTOM_TYPE'(0);
        end
        if (write_data_in != CUSTOM_TYPE'(0)) begin
            registers[0] = write_data_in;
        end
    end
    always_comb begin
        CUSTOM_TYPE current_read_data = CUSTOM_TYPE'(0);
        int offset = (internal_addr - BASE_ADDR) / ($bits(CUSTOM_TYPE)/8);
        if (internal_addr >= BASE_ADDR && internal_addr < BASE_ADDR + TOTAL_SIZE) begin
            if (offset >= 0 && offset < REG_COUNT) begin
                current_read_data = registers[offset];
            end
        end
        read_data_out = current_read_data;
    end
endmodule
module HierBlockUser (
    input logic [15:0] ext_addr,
    input logic [7:0] ext_data_in,
    output logic [7:0] ext_data_out
);
    HierBlockParamModule #(
        .CUSTOM_TYPE(logic [7:0])
    ) default_hbp (
        .addr_in(ext_addr),
        .write_data_in(ext_data_in),
        .read_data_out(ext_data_out)
    );
    HierBlockParamModule #(
        .BASE_ADDR(16'h2000),
        .REG_COUNT(8),
        .CUSTOM_TYPE(logic [7:0]),
        .BLOCK_NAME("SPECIAL"),
        .DELAY_FACTOR(2.5)
    ) special_hbp (
        .addr_in(ext_addr),
        .write_data_in(ext_data_in),
        .read_data_out(ext_data_out)
    );
    HierBlockParamModule #(
        .BASE_ADDR(16'h3000),
        .REG_COUNT(2),
        .CUSTOM_TYPE(logic [15:0]),
        .BLOCK_NAME("CUSTOM_BLOCK"),
        .DELAY_FACTOR(1.0)
    ) custom_hbp (
        .addr_in(ext_addr),
        .write_data_in({8'h00, ext_data_in}),
        .read_data_out(ext_data_out)
    );
endmodule
module InnerCell (
    input logic [7:0] i_data,
    output logic [7:0] o_data
);
    assign o_data = i_data + 1;
endmodule
module CellArrayRefTest #(
    parameter int N_INSTANCES = 2
) (
    input logic [7:0] in_data,
    output logic [7:0] out_data
);
    logic [7:0] inner_data_array [N_INSTANCES-1:0];
    generate
        for (genvar i = 0; i < N_INSTANCES; i++) begin : gen_inst
            InnerCell inst_i (
                .i_data(in_data + i),
                .o_data(inner_data_array[i])
            );
        end
    endgenerate
    assign out_data = inner_data_array[N_INSTANCES-1];
endmodule
