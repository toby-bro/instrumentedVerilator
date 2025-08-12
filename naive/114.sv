typedef enum logic [1:0] {
    MODE_ADD,
    MODE_SUB,
    MODE_MUL,
    MODE_DIV
} OperationMode_t;
typedef struct packed {
    logic [7:0] code;
    bit         error;
    bit         valid;
} Status_t;
typedef union packed {
    logic [15:0] full_word;
    struct packed {
        logic [7:0] lo_byte;
        logic [7:0] hi_byte;
    } bytes;
} WordOrBytes_t;
class MyDataClass;
    rand int data_id;
    int value;
    function new(int id, int val);
        this.data_id = id;
        this.value = val;
    endfunction
endclass
module CombinationalLogicProcessor (
    input  logic [7:0] a_in,
    input  logic [7:0] b_in,
    input  logic [1:0] op_sel,
    output logic [8:0] result_out,
    output logic [2:0] status_flags
);
    logic [7:0] intermediate_res;
    logic       zero_flag;
    logic       negative_flag;
    logic       overflow_flag;
    assign zero_flag = (intermediate_res == 8'b0);
    always_comb begin
        intermediate_res = 8'b0;
        status_flags     = 3'b0;
        case (op_sel)
            2'b00: begin
                intermediate_res = a_in + b_in;
                overflow_flag = (a_in[7] == b_in[7]) && (intermediate_res[7] != a_in[7]);
            end
            2'b01: begin
                intermediate_res = a_in - b_in;
                overflow_flag = (a_in[7] != b_in[7]) && (intermediate_res[7] != a_in[7]);
            end
            2'b10: begin
                intermediate_res = a_in & b_in;
                overflow_flag = 1'b0;
            end
            2'b11: begin
                intermediate_res = a_in | b_in;
                overflow_flag = 1'b0;
            end
            default: begin
                intermediate_res = 8'b0;
                overflow_flag = 1'b0;
            end
        endcase
        negative_flag = intermediate_res[7];
        status_flags[0] = zero_flag;
        status_flags[1] = negative_flag;
        status_flags[2] = overflow_flag;
        result_out = {1'b0, intermediate_res};
    end
endmodule
module SequentialRegisterArray (
    input  logic        clk,
    input  logic        reset_n,
    input  logic [7:0]  data_in,
    input  logic        write_en,
    input  logic [3:0]  addr_in,
    output logic [7:0]  data_out
);
    localparam RAM_DEPTH = 16;
    logic [7:0] memory_array [0:RAM_DEPTH-1];
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            for (int i = 0; i < RAM_DEPTH; i++) begin
                memory_array[i] <= 8'h00;
            end
        end else begin
            if (write_en) begin
                memory_array[addr_in] <= data_in;
            end
        end
    end
    assign data_out = memory_array[addr_in];
endmodule
module TypeDefinitionProcessor (
    input  logic [7:0] input_val,
    input  logic [1:0] op_mode,
    input  real        coeff_in,
    output logic [15:0] output_res,
    output Status_t     status_info,
    output real         scaled_coeff_out
);
    typedef logic [3:0] FourBitArray_t [2];
    FourBitArray_t  my_array;
    MyDataClass     my_object;
    logic [7:0]     history_q[$];
    WordOrBytes_t   union_var;
    OperationMode_t current_op;
    real internal_real_val;
    always_comb begin
        output_res = 16'b0;
        status_info = '{code: 8'h00, error: 1'b0, valid: 1'b0};
        current_op = OperationMode_t'(op_mode);
        scaled_coeff_out = coeff_in * 2.0;
        internal_real_val = 1.0 / coeff_in;
        my_object = new(input_val, input_val * 2);
        if (my_object != null) begin
            output_res = my_object.value + my_object.data_id;
        end else begin
            output_res = 16'hFFFF;
        end
        if (input_val != 8'h00) begin
            history_q.push_front(input_val);
            if (history_q.size() > 5) begin
                void'(history_q.pop_back());
            end
        end
        my_array[0] = input_val[3:0];
        my_array[1] = input_val[7:4];
        union_var.full_word = {input_val, input_val + 1};
        if (union_var.bytes.hi_byte == union_var.bytes.lo_byte) begin
            status_info.error = 1'b1;
        end
        case (current_op)
            MODE_ADD: begin
                output_res = output_res + input_val;
                status_info.code = 8'h01;
                status_info.valid = 1'b1;
            end
            MODE_SUB: begin
                output_res = output_res - input_val;
                status_info.code = 8'h02;
                status_info.valid = 1'b1;
            end
            MODE_MUL: begin
                output_res = output_res * input_val;
                status_info.code = 8'h03;
                status_info.valid = 1'b1;
                if (output_res > 16'hFFF0) status_info.error = 1'b1;
            end
            MODE_DIV: begin
                if (input_val != 8'b0) begin
                    output_res = output_res / input_val;
                    status_info.code = 8'h04;
                    status_info.valid = 1'b1;
                end else begin
                    status_info.code = 8'hFF;
                    status_info.error = 1'b1;
                end
            end
            default: begin
            end
        endcase
    end
endmodule
module ProceduralFunctionTask (
    input  logic [7:0] input_a,
    input  logic [7:0] input_b,
    input  logic [7:0] input_c,
    input  logic       enable_task,
    output logic [15:0] output_sum,
    output logic [15:0] output_mult,
    output logic [15:0] output_final
);
    function automatic logic [7:0] my_adder_func(input logic [7:0] val1, input logic [7:0] val2);
        logic [7:0] temp_sum;
        temp_sum = val1 + val2;
        return temp_sum;
    endfunction
    task automatic my_multiplier_task(input logic [7:0] m_val1, input logic [7:0] m_val2, output logic [15:0] m_result);
        m_result = m_val1 * m_val2;
        if (m_val1 > 50) begin
            for (int i = 0; i < 3; i++) begin
                m_result = m_result + i;
            end
        end
    endtask
    logic [7:0] local_sum;
    logic [15:0] local_mult;
    logic [15:0] loop_accum;
    logic [7:0] input_sum;
    assign input_sum = input_a + input_b;
    always_comb begin
        automatic int counter;
        counter = 0;
        local_sum = my_adder_func(input_a, input_b);
        output_sum = {8'b0, local_sum};
        loop_accum = 16'b0;
        while (counter < 4 && enable_task) begin
            loop_accum = loop_accum + counter;
            counter++;
        end
        if (enable_task) begin
            my_multiplier_task(input_sum, input_c, local_mult);
        end else begin
            local_mult = 16'b0;
        end
        output_mult = local_mult;
        output_final = output_sum + output_mult + loop_accum;
    end
endmodule
module ParameterGenerateExample #(
    parameter DATA_WIDTH = 8,
    parameter DEPTH_LOG2 = 3
) (
    input  logic [DATA_WIDTH-1:0] data_in,
    input  logic [DEPTH_LOG2-1:0] index_in,
    output logic [DATA_WIDTH-1:0] data_out,
    output logic                  parity_check
);
    localparam DEPTH = 1 << DEPTH_LOG2;
    logic [DATA_WIDTH-1:0] storage_elements [0:DEPTH-1];
    logic                  parity_bits      [0:DEPTH-1];
    genvar i;
    generate
        for (i = 0; i < DEPTH; i++) begin : gen_data_path
            assign storage_elements[i] = data_in + i;
            if (i % 2 == 0) begin : gen_even_parity
                always_comb begin
                    parity_bits[i] = ^storage_elements[i];
                end
            end else begin : gen_odd_placeholder
                assign parity_bits[i] = 1'b0;
            end
        end
    endgenerate
    assign data_out = storage_elements[index_in];
    assign parity_check = parity_bits[index_in];
endmodule
module SimpleAssertions (
    input  logic       clk,
    input  logic       reset_n,
    input  logic [3:0] input_val,
    input  logic       start_op,
    input  logic       data_ready,
    output logic       output_status
);
    logic internal_state;
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            internal_state <= 1'b0;
            output_status <= 1'b0;
        end else begin
            if (start_op) begin
                internal_state <= 1'b1;
            end else if (data_ready) begin
                internal_state <= 1'b0;
                assert (input_val < 10) else $error("Input value %0d is too high!", input_val);
            end
            output_status <= internal_state;
        end
    end
    property p_data_ready_eventual;
        @(posedge clk) (start_op && !reset_n) |=> ##[1:2] data_ready;
    endproperty
    assert property (p_data_ready_eventual) else $error("Property p_data_ready_eventual failed!");
    property p_zero_input_status;
        @(posedge clk) (input_val == 4'b0 && !reset_n) |-> ##1 (output_status == 1'b0);
    endproperty
    assert property (p_zero_input_status) else $error("Property p_zero_input_status failed!");
endmodule
interface SimpleBusInterface;
    logic        clk;
    logic        reset_n;
    logic [7:0]  addr;
    logic [15:0] wdata;
    logic [15:0] rdata;
    logic        write_en;
    logic        read_en;
    logic        ready;
    modport master (
        output addr, wdata, write_en, read_en,
        input  clk, reset_n, rdata, ready
    );
    modport slave (
        input  addr, wdata, write_en, read_en,
        output rdata, ready,
        input  clk, reset_n
    );
endinterface
module InterfaceMasterConsumer (
    input  logic       clk,
    input  logic       reset_n,
    output logic [7:0] addr,
    output logic [15:0] wdata,
    output logic       write_en,
    output logic       read_en,
    input  logic [15:0] rdata,
    input  logic       ready,
    input  logic       start_transaction,
    output logic       transaction_done
);
    logic [7:0]  current_addr;
    logic [15:0] data_to_write;
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            write_en <= 1'b0;
            read_en  <= 1'b0;
            addr     <= 8'h00;
            wdata    <= 16'h0000;
            current_addr       <= 8'h00;
            data_to_write      <= 16'h0000;
            transaction_done   <= 1'b0;
        end else begin
            write_en <= 1'b0;
            read_en  <= 1'b0;
            transaction_done   <= 1'b0;
            if (start_transaction) begin
                if (!ready) begin
                end else begin
                    addr <= current_addr;
                    wdata <= data_to_write;
                    write_en <= 1'b1;
                    if (current_addr < 8'hFF) begin
                        current_addr <= current_addr + 1;
                        data_to_write <= data_to_write + 1;
                    end else begin
                        transaction_done <= 1'b1;
                    end
                end
            end else if (ready) begin
                read_en <= 1'b1;
                addr <= 8'h10;
            end
        end
    end
endmodule
module InterfaceSlaveConsumer (
    input  logic       clk,
    input  logic       reset_n,
    input  logic [7:0] addr,
    input  logic [15:0] wdata,
    input  logic       write_en,
    input  logic       read_en,
    output logic [15:0] rdata,
    output logic       ready,
    input  logic       data_in_from_system,
    output logic [15:0] data_out_to_system
);
    logic [15:0] internal_reg;
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            internal_reg <= 16'hABCD;
            rdata <= 16'hXXXX;
            ready <= 1'b0;
            data_out_to_system <= 16'h0000;
        end else begin
            ready <= 1'b1;
            if (write_en) begin
                internal_reg <= wdata;
                data_out_to_system <= wdata;
            end else if (read_en) begin
                rdata <= internal_reg;
            end else begin
                rdata <= 16'h0000;
            end
            if (data_in_from_system) begin
                internal_reg <= internal_reg + 1;
            end
        end
    end
endmodule
