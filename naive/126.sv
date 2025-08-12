interface axi_lite_if #(
    parameter ADDR_WIDTH = 32,
    parameter DATA_WIDTH = 32
);
    logic [ADDR_WIDTH-1:0] awaddr;
    logic awvalid;
    logic awready;
    logic [DATA_WIDTH-1:0] wdata;
    logic wvalid;
    logic wready;
    logic [1:0] bresp;
    logic bvalid;
    logic bready;
    logic [ADDR_WIDTH-1:0] araddr;
    logic arvalid;
    logic arready;
    logic [DATA_WIDTH-1:0] rdata;
    logic [1:0] rresp;
    logic rvalid;
    logic rready;
    modport master (
        output awaddr, output awvalid, input awready,
        output wdata, output wvalid, input wready,
        input bresp, input bvalid, output bready,
        output araddr, output arvalid, input arready,
        input rdata, input rresp, input rvalid, output rready
    );
    modport slave (
        input awaddr, input awvalid, output awready,
        input wdata, input wvalid, output wready,
        output bresp, output bvalid, input bready,
        input araddr, input arvalid, output arready,
        output rdata, output rresp, output rvalid, input rready
    );
endinterface
class Packet;
    typedef enum {
        TYPE_A,
        TYPE_B,
        TYPE_C
    } packet_type_e;
    bit [7:0] header;
    bit [15:0] payload_len;
    bit [7:0] data_checksum;
    packet_type_e p_type;
    function new(packet_type_e type_in);
        p_type = type_in;
        header = 8'hAA;
        payload_len = 16'h1000;
        data_checksum = 8'hFF;
    endfunction
    function int calculate_checksum();
        return (header + payload_len[7:0] + payload_len[15:8] + data_checksum);
    endfunction
endclass
typedef struct packed {
    logic [7:0] field1;
    logic [15:0] field2;
    logic [3:0] field3;
} MyPackedStruct_t;
typedef union packed {
    logic [31:0] all_bits;
    struct packed {
        logic [15:0] low;
        logic [15:0] high;
    } halves;
    struct packed {
        logic [7:0] byte0;
        logic [7:0] byte1;
        logic [7:0] byte2;
        logic [7:0] byte3;
    } bytes;
} MyPackedUnion_t;
module CombinationalLogicParamEnum (
    input logic [7:0] in_data_a,
    input logic [7:0] in_data_b,
    input logic select_op,
    output logic [15:0] out_result_comb,
    output logic [7:0] out_parity_calc
);
    parameter DATA_WIDTH = 8;
    parameter RESULT_WIDTH = 16;
    typedef enum logic [1:0] {
        OP_ADD = 2'b00,
        OP_SUB = 2'b01,
        OP_MUL = 2'b10,
        OP_DIV = 2'b11
    } OperationType_e;
    OperationType_e current_op;
    logic [RESULT_WIDTH-1:0] intermediate_res;
    logic [DATA_WIDTH-1:0] temp_parity;
    assign current_op = select_op ? OP_MUL : OP_ADD;
    always_comb begin
        case (current_op)
            OP_ADD: intermediate_res = in_data_a + in_data_b;
            OP_SUB: intermediate_res = in_data_a - in_data_b;
            OP_MUL: intermediate_res = in_data_a * in_data_b;
            OP_DIV: intermediate_res = (in_data_b == 0) ? 0 : (in_data_a / in_data_b);
            default: intermediate_res = 0;
        endcase
    end
    always_comb begin
        temp_parity = 0;
        for (int i = 0; i < DATA_WIDTH; i++) begin
            if (in_data_a[i]) begin
                temp_parity = temp_parity + 1;
            end
        end
        out_parity_calc = temp_parity;
    end
    assign out_result_comb = intermediate_res;
endmodule
module SequentialLogicStructUnion (
    input logic clk,
    input logic rst_n,
    input MyPackedStruct_t in_struct_data,
    input MyPackedUnion_t in_union_data,
    output MyPackedStruct_t out_struct_reg,
    output MyPackedUnion_t out_union_reg,
    output logic [31:0] union_byte_sum
);
    MyPackedStruct_t internal_struct_reg;
    MyPackedUnion_t internal_union_reg;
    logic [31:0] internal_byte_sum;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            internal_struct_reg.field1 <= 0;
            internal_struct_reg.field2 <= 0;
            internal_struct_reg.field3 <= 0;
            internal_union_reg.all_bits <= 0;
        end else begin
            internal_struct_reg <= in_struct_data;
            internal_union_reg <= in_union_data;
        end
    end
    always_comb begin
        internal_byte_sum = internal_union_reg.bytes.byte0 +
                            internal_union_reg.bytes.byte1 +
                            internal_union_reg.bytes.byte2 +
                            internal_union_reg.bytes.byte3;
    end
    assign out_struct_reg = internal_struct_reg;
    assign out_union_reg = internal_union_reg;
    assign union_byte_sum = internal_byte_sum;
endmodule
module ClassUsageModule (
    input logic clk,
    input logic rst_n,
    input logic class_instantiate_enable,
    input logic [7:0] packet_type_sel,
    output logic [31:0] out_packet_checksum
);
    Packet my_packet;
    logic [31:0] calculated_checksum;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            my_packet = null;
            calculated_checksum <= 0;
        end else begin
            if (class_instantiate_enable) begin
                Packet::packet_type_e p_type_val;
                case (packet_type_sel)
                    8'd0: p_type_val = Packet::TYPE_A;
                    8'd1: p_type_val = Packet::TYPE_B;
                    default: p_type_val = Packet::TYPE_C;
                endcase
                if (my_packet == null) begin
                    my_packet = new(p_type_val);
                end else begin
                    my_packet.p_type = p_type_val;
                end
                calculated_checksum <= my_packet.calculate_checksum();
            end else begin
                my_packet = null;
                calculated_checksum <= 0;
            end
        end
    end
    assign out_packet_checksum = calculated_checksum;
endmodule
module InterfaceUserModule (
    input logic clk,
    input logic rst_n,
    input logic [31:0] awaddr_i,
    input logic awvalid_i,
    output logic awready_o,
    input logic [31:0] wdata_i,
    input logic wvalid_i,
    output logic wready_o,
    output logic [1:0] bresp_o,
    output logic bvalid_o,
    input logic bready_i,
    input logic [31:0] araddr_i,
    input logic arvalid_i,
    output logic arready_o,
    output logic [31:0] rdata_o,
    output logic [1:0] rresp_o,
    output logic rvalid_o,
    input logic rready_i,
    output logic [31:0] read_data_out,
    output logic [31:0] write_addr_reg,
    output logic [31:0] write_data_reg
);
    axi_lite_if #(.ADDR_WIDTH(32), .DATA_WIDTH(32)) s_if_inst();
    assign s_if_inst.awaddr = awaddr_i;
    assign s_if_inst.awvalid = awvalid_i;
    assign awready_o = s_if_inst.awready;
    assign s_if_inst.wdata = wdata_i;
    assign s_if_inst.wvalid = wvalid_i;
    assign wready_o = s_if_inst.wready;
    assign bresp_o = s_if_inst.bresp;
    assign bvalid_o = s_if_inst.bvalid;
    assign s_if_inst.bready = bready_i;
    assign s_if_inst.araddr = araddr_i;
    assign s_if_inst.arvalid = arvalid_i;
    assign arready_o = s_if_inst.arready;
    assign rdata_o = s_if_inst.rdata;
    assign rresp_o = s_if_inst.rresp;
    assign rvalid_o = s_if_inst.rvalid;
    assign s_if_inst.rready = rready_i;
    logic [31:0] internal_reg_data;
    logic [31:0] internal_addr_reg;
    logic [31:0] internal_wdata_reg;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            s_if_inst.awready <= 1'b0;
            s_if_inst.wready <= 1'b0;
            s_if_inst.bvalid <= 1'b0;
            s_if_inst.bresp <= 2'b00;
            internal_addr_reg <= 0;
            internal_wdata_reg <= 0;
        end else begin
            s_if_inst.awready <= 1'b1;
            s_if_inst.wready <= 1'b1;
            if (s_if_inst.awvalid && s_if_inst.awready) begin
                internal_addr_reg <= s_if_inst.awaddr;
            end
            if (s_if_inst.wvalid && s_if_inst.wready) begin
                internal_wdata_reg <= s_if_inst.wdata;
            end
            if (s_if_inst.awvalid && s_if_inst.wvalid && s_if_inst.awready && s_if_inst.wready) begin
                s_if_inst.bvalid <= 1'b1;
                s_if_inst.bresp <= 2'b00;
            end else if (s_if_inst.bvalid && s_if_inst.bready) begin
                s_if_inst.bvalid <= 1'b0;
            end
        end
    end
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            s_if_inst.arready <= 1'b0;
            s_if_inst.rvalid <= 1'b0;
            s_if_inst.rdata <= 0;
            s_if_inst.rresp <= 2'b00;
            internal_reg_data <= 32'hFEEDFACE;
        end else begin
            s_if_inst.arready <= 1'b1;
            if (s_if_inst.arvalid && s_if_inst.arready) begin
                s_if_inst.rdata <= internal_reg_data;
                s_if_inst.rvalid <= 1'b1;
                s_if_inst.rresp <= 2'b00;
            end else if (s_if_inst.rvalid && s_if_inst.rready) begin
                s_if_inst.rvalid <= 1'b0;
            end
        end
    end
    assign read_data_out = s_if_inst.rdata;
    assign write_addr_reg = internal_addr_reg;
    assign write_data_reg = internal_wdata_reg;
endmodule
module MemoryQueueArrayModule (
    input logic clk,
    input logic rst_n,
    input logic [3:0] addr_in,
    input logic [7:0] data_in_mem,
    input logic mem_wr_en,
    input logic [7:0] queue_push_data,
    input logic queue_push_en,
    input logic queue_pop_en,
    input logic [7:0] dyn_arr_data,
    input logic dyn_arr_push_en,
    input logic [3:0] assoc_array_lookup_key_in, 
    output logic [7:0] mem_data_out,
    output logic [7:0] queue_pop_data,
    output logic queue_empty,
    output logic [7:0] dyn_arr_last_val,
    output logic [7:0] assoc_array_val_out 
);
    parameter MEM_DEPTH = 16;
    logic [7:0] internal_memory [0:MEM_DEPTH-1]; 
    logic [7:0] data_associative_array [int];
    parameter QUEUE_SIZE = 8;
    logic [7:0] queue_storage [0:QUEUE_SIZE-1];
    logic [$clog2(QUEUE_SIZE+1)-1:0] head_ptr, tail_ptr;
    logic [$clog2(QUEUE_SIZE+1)-1:0] queue_count;
    logic queue_full_comb;
    logic queue_empty_comb;
    parameter DYN_ARR_MAX_SIZE = 8;
    logic [7:0] fixed_dynamic_array [0:DYN_ARR_MAX_SIZE-1];
    logic [$clog2(DYN_ARR_MAX_SIZE+1)-1:0] dyn_arr_current_size;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            for (int i=0; i<MEM_DEPTH; i++) begin
                internal_memory[i] <= 8'h00; 
            end
        end else begin
            if (mem_wr_en) begin
                internal_memory[addr_in] <= data_in_mem;
            end
        end
    end
    assign mem_data_out = internal_memory[addr_in];
    always_comb begin
        data_associative_array[0] = 8'h11;
        data_associative_array[1] = 8'h22;
        data_associative_array[2] = data_in_mem; 
        if (data_associative_array.exists(assoc_array_lookup_key_in)) begin
            assoc_array_val_out = data_associative_array[assoc_array_lookup_key_in];
        end else begin
            assoc_array_val_out = 8'hXX; 
        end
    end
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            head_ptr <= 0;
            tail_ptr <= 0;
            queue_count <= 0;
        end else begin
            logic push_op = queue_push_en && !queue_full_comb;
            logic pop_op = queue_pop_en && !queue_empty_comb;
            if (push_op && !pop_op) begin 
                queue_storage[tail_ptr] <= queue_push_data;
                tail_ptr <= (tail_ptr == QUEUE_SIZE - 1) ? 0 : tail_ptr + 1;
                queue_count <= queue_count + 1;
            end else if (!push_op && pop_op) begin 
                head_ptr <= (head_ptr == QUEUE_SIZE - 1) ? 0 : head_ptr + 1;
                queue_count <= queue_count - 1;
            end else if (push_op && pop_op) begin 
                queue_storage[tail_ptr] <= queue_push_data;
                tail_ptr <= (tail_ptr == QUEUE_SIZE - 1) ? 0 : tail_ptr + 1;
                head_ptr <= (head_ptr == QUEUE_SIZE - 1) ? 0 : head_ptr + 1;
            end
        end
    end
    always_comb begin
        queue_full_comb = (queue_count == QUEUE_SIZE);
        queue_empty_comb = (queue_count == 0);
        queue_pop_data = queue_empty_comb ? 8'hXX : queue_storage[head_ptr];
        queue_empty = queue_empty_comb;
    end
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            for (int i=0; i<DYN_ARR_MAX_SIZE; i++) fixed_dynamic_array[i] <= 0;
            dyn_arr_current_size <= 0;
        end else begin
            if (dyn_arr_push_en && dyn_arr_current_size < DYN_ARR_MAX_SIZE) begin
                fixed_dynamic_array[dyn_arr_current_size] <= dyn_arr_data;
                dyn_arr_current_size <= dyn_arr_current_size + 1;
            end
        end
    end
    always_comb begin
        dyn_arr_last_val = (dyn_arr_current_size > 0) ? fixed_dynamic_array[dyn_arr_current_size - 1] : 8'h00;
    end
endmodule
module FunctionTaskAssertionModule (
    input logic [7:0] in_val_a,
    input logic [7:0] in_val_b,
    input logic assertion_check_en,
    output logic [15:0] func_result_out,
    output logic [15:0] task_result_out,
    output logic [7:0] complex_op_out
);
    function automatic int sum_two_numbers(int a, int b);
        return a + b;
    endfunction
    task automatic calculate_complex_op(input logic [7:0] val1, input logic [7:0] val2, output logic [7:0] result_op);
        logic [7:0] temp_res;
        temp_res = val1 * val2;
        if (temp_res > 200) begin
            result_op = temp_res - 50;
        end else begin
            result_op = temp_res + 10;
        end
    endtask
    logic [7:0] complex_output_reg;
    logic [15:0] func_res;
    logic [15:0] task_res;
    always_comb begin
        func_res = sum_two_numbers(in_val_a, in_val_b);
        calculate_complex_op(in_val_a, in_val_b, complex_output_reg);
        task_res = complex_output_reg + in_val_a;
    end
    assign func_result_out = func_res;
    assign task_result_out = task_res;
    assign complex_op_out = complex_output_reg;
    always_comb begin
        if (assertion_check_en) begin
            assert (in_val_a + in_val_b <= 255);
        end
    end
    always_comb begin
        assert (in_val_a != in_val_b) else $error("Assertion failed: in_val_a equals in_val_b!");
    end
endmodule
module GenerateComplexModule (
    input logic clk,
    input logic rst_n,
    input logic [3:0] selector_in,
    input logic [7:0] data_in_gen,
    output logic [7:0] out_data_gen,
    output logic [7:0] parity_out_gen
);
    parameter NUM_SLICES = 4;
    logic [7:0] internal_data_reg [NUM_SLICES-1:0];
    logic [7:0] parity_per_slice [NUM_SLICES-1:0];
    generate
        for (genvar i = 0; i < NUM_SLICES; i++) begin : gen_slice
            always_ff @(posedge clk or negedge rst_n) begin
                if (!rst_n) begin
                    internal_data_reg[i] <= 0; 
                end else begin
                    internal_data_reg[i] <= data_in_gen + i;
                end
            end
            if (i == 0) begin : gen_first_slice
                always_comb begin
                    parity_per_slice[i] = ^internal_data_reg[i]; 
                end
            end else if (i == 1) begin : gen_second_slice
                assign parity_per_slice[i] = ~internal_data_reg[i]; 
            end else begin : gen_other_slices
                assign parity_per_slice[i] = internal_data_reg[i] | (internal_data_reg[i] >> 4); 
            end
        end
    endgenerate
    always_comb begin
        if (selector_in < NUM_SLICES) begin
            out_data_gen = internal_data_reg[selector_in];
            parity_out_gen = parity_per_slice[selector_in];
        end else begin
            out_data_gen = 8'hFF;
            parity_out_gen = 8'h00;
        end
    end
endmodule
