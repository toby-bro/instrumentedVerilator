interface axi_lite_if (
    input logic clk,
    input logic rst_n
);
    logic [31:0] awaddr;
    logic [ 2:0] awprot;
    logic        awvalid;
    logic        awready;
    logic [31:0] wdata;
    logic [ 3:0] wstrb;
    logic        wvalid;
    logic        wready;
    logic [ 1:0] bresp;
    logic        bvalid;
    logic        bready;
    logic [31:0] araddr;
    logic [ 2:0] arprot;
    logic        arvalid;
    logic        arready;
    logic [31:0] rdata;
    logic [ 1:0] rresp;
    logic        rvalid;
    logic        rready;
    modport Master (
        output awaddr, awprot, awvalid, wdata, wstrb, wvalid, bready, araddr, arprot, arvalid, rready,
        input  awready, wready, bresp, bvalid, rdata, rresp, rvalid
    );
    modport Slave (
        input  awaddr, awprot, awvalid, wdata, wstrb, wvalid, bready, araddr, arprot, arvalid, rready,
        output awready, wready, bresp, bvalid, rdata, rresp, rvalid
    );
endinterface
class MyDataStore;
    rand int data_val;
    function new();
        data_val = 0;
    endfunction
    function void set_data(int val);
        data_val = val;
    endfunction
    function int get_data();
        return data_val;
    endfunction
endclass
module CombinationalLogic (
    input logic [7:0] in_a,
    input logic [7:0] in_b,
    input logic       sel_mode,
    output logic [7:0] out_res
);
    logic [7:0] temp_sum;
    logic [7:0] temp_diff;
    assign temp_sum = in_a + in_b;
    assign temp_diff = in_a - in_b;
    always_comb begin
        if (sel_mode) begin
            out_res = temp_sum;
        end else begin
            out_res = temp_diff;
        end
    end
endmodule
module SimpleRegister (
    input  logic        clk,
    input  logic        rst_n,
    input  logic [15:0] data_in,
    output logic [15:0] data_out
);
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            data_out <= 16'h0000;
        end else begin
            data_out <= data_in;
        end
    end
endmodule
module RamBlock #(
    parameter ADDR_WIDTH = 4,
    parameter DATA_WIDTH = 8
) (
    input  logic                     clk,
    input  logic                     write_en,
    input  logic [ADDR_WIDTH-1:0]    read_addr,
    input  logic [ADDR_WIDTH-1:0]    write_addr,
    input  logic [DATA_WIDTH-1:0]    data_in,
    output logic [DATA_WIDTH-1:0]    data_out
);
    localparam RAM_DEPTH = 1 << ADDR_WIDTH;
    logic [DATA_WIDTH-1:0] mem [RAM_DEPTH-1:0];
    always_ff @(posedge clk) begin
        if (write_en) begin
            mem[write_addr] <= data_in;
        end
    end
    assign data_out = mem[read_addr];
endmodule
module ComplexLogicWithTypes (
    input  logic [7:0] op1_i,
    input  logic [7:0] op2_i,
    input  logic       control_i,
    output logic [15:0] result_o
);
    typedef enum logic [1:0] {
        ADD_OP,
        SUB_OP,
        MUL_OP,
        DIV_OP
    } operation_e;
    typedef struct packed {
        logic [7:0] operand1;
        logic [7:0] operand2;
        operation_e op_type;
    } math_cmd_t;
    math_cmd_t current_cmd;
    function automatic logic [15:0] calculate (math_cmd_t cmd);
        logic [15:0] res_func = 0;
        case (cmd.op_type)
            ADD_OP: res_func = cmd.operand1 + cmd.operand2;
            SUB_OP: res_func = cmd.operand1 - cmd.operand2;
            MUL_OP: res_func = cmd.operand1 * cmd.operand2;
            DIV_OP: begin
                if (cmd.operand2 != 0) res_func = cmd.operand1 / cmd.operand2;
                else res_func = 16'hFFFF;
            end
            default: res_func = 0;
        endcase
        return res_func;
    endfunction
    always_comb begin
        if (control_i) begin
            current_cmd.operand1 = op1_i;
            current_cmd.operand2 = op2_i;
            current_cmd.op_type  = MUL_OP;
        end else begin
            current_cmd.operand1 = op1_i;
            current_cmd.operand2 = op2_i;
            current_cmd.op_type  = ADD_OP;
        end
        result_o = calculate(current_cmd);
    end
endmodule
module InterfaceUserModule (
    input  logic        awready_i,
    input  logic        wready_i,
    input  logic [1:0]  bresp_i,
    input  logic        bvalid_i,
    input  logic [31:0] rdata_i,
    input  logic [1:0]  rresp_i,
    input  logic        rvalid_i,
    input  logic [31:0] master_awaddr_in,
    input  logic [31:0] master_wdata_in,
    input  logic [3:0]  master_wstrb_in,
    input  logic        master_awvalid_in,
    input  logic        master_wvalid_in,
    input  logic [31:0] master_araddr_in,
    input  logic        master_arvalid_in,
    input  logic        master_bready_in,
    input  logic        master_rready_in,
    output logic [31:0] awaddr_o,
    output logic [2:0]  awprot_o,
    output logic        awvalid_o,
    output logic [31:0] wdata_o,
    output logic [3:0]  wstrb_o,
    output logic        wvalid_o,
    output logic        bready_o,
    output logic [31:0] araddr_o,
    output logic [2:0]  arprot_o,
    output logic        arvalid_o,
    output logic        rready_o,
    output logic [31:0] read_data_out
);
    always_comb begin
        awaddr_o  = master_awaddr_in;
        awprot_o  = 3'b000;
        awvalid_o = master_awvalid_in;
        wdata_o   = master_wdata_in;
        wstrb_o   = master_wstrb_in;
        wvalid_o  = master_wvalid_in;
        bready_o  = master_bready_in;
        araddr_o  = master_araddr_in;
        arprot_o  = 3'b000;
        arvalid_o = master_arvalid_in;
        rready_o  = master_rready_in;
        read_data_out = rdata_i;
    end
endmodule
module ClassInstantiationModule (
    input  logic        clk,
    input  logic        trigger_update_i,
    input  int          new_value_i,
    output int          stored_value_o
);
    MyDataStore my_object_handle;
    always_ff @(posedge clk) begin
        if (my_object_handle == null) begin
            my_object_handle = new();
        end
        if (trigger_update_i) begin
            my_object_handle.set_data(new_value_i);
        end
    end
    always_comb begin
        if (my_object_handle != null) begin
            stored_value_o = my_object_handle.get_data();
        end else begin
            stored_value_o = 0;
        end
    end
endmodule
module ArrayManipulation (
    input  logic        clk,
    input  logic [7:0]  data_in_i,
    input  logic [2:0]  write_index_i,
    input  logic        write_en_i,
    input  logic [2:0]  read_index_i,
    output logic [7:0]  data_out_o,
    output logic [3:0]  nibble_out_o
);
    logic [7:0] unpacked_array [8];
    typedef struct packed {
        logic [3:0] nibble0;
        logic [3:0] nibble1;
    } s_packed_byte;
    s_packed_byte packed_data_storage [4];
    logic [7:0] dynamic_array [];
    always_ff @(posedge clk) begin
        if (write_en_i) begin
            unpacked_array[write_index_i] <= data_in_i;
            packed_data_storage[write_index_i].nibble0 <= data_in_i[3:0];
            packed_data_storage[write_index_i].nibble1 <= data_in_i[7:4];
        end
    end
    always_comb begin
        if (read_index_i < $size(unpacked_array)) begin
            data_out_o = unpacked_array[read_index_i];
        end else begin
            data_out_o = 8'hFF;
        end
        if (read_index_i < $size(packed_data_storage)) begin
            nibble_out_o = packed_data_storage[read_index_i].nibble0;
        end else begin
            nibble_out_o = 4'hF;
        end
    end
endmodule
module GenericArithmetic #(
    parameter DATA_WIDTH = 16,
    parameter OP_MODE    = 0
) (
    input  logic [DATA_WIDTH-1:0] input_a,
    input  logic [DATA_WIDTH-1:0] input_b,
    output logic [DATA_WIDTH-1:0] output_result
);
    generate
        if (OP_MODE == 0) begin : add_block
            assign output_result = input_a + input_b;
        end else if (OP_MODE == 1) begin : sub_block
            assign output_result = input_a - input_b;
        end else begin : default_block
            assign output_result = {DATA_WIDTH{1'bx}};
        end
    endgenerate
endmodule
module SimpleAssertions (
    input  logic clk,
    input  logic rst_n,
    input  logic request_i,
    input  logic grant_i,
    output logic grant_o
);
    logic internal_grant_reg;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            internal_grant_reg <= 1'b0;
        end else if (request_i && !internal_grant_reg) begin
            internal_grant_reg <= 1'b1;
        end else if (grant_i && internal_grant_reg) begin
            internal_grant_reg <= 1'b0;
        end
    end
    assign grant_o = internal_grant_reg;
    property p_request_leads_to_grant;
        @(posedge clk) disable iff (!rst_n) (request_i ##1 request_i) |-> grant_i;
    endproperty
    assert property (p_request_leads_to_grant);
    property p_grant_no_unrequested;
        @(posedge clk) disable iff (!rst_n) (!request_i ##1 grant_i) |-> !grant_i;
    endproperty
    assert property (p_grant_no_unrequested);
endmodule
