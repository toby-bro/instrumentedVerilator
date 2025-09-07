module DataOpsAndTypes (
    input logic [7:0] in_a,
    input logic [7:0] in_b,
    input logic in_sel,
    output logic [15:0] out_result,
    output logic [2:0] out_status
);
    parameter P_WIDTH = 8;
    localparam L_DEPTH = 4;
    typedef enum logic [1:0] {
        ST_IDLE,
        ST_BUSY,
        ST_DONE,
        ST_ERROR
    } state_e;
    typedef struct packed {
        logic [P_WIDTH-1:0] val1;
        logic [P_WIDTH-1:0] val2;
        int                 idx;
    } my_struct_t;
    logic [P_WIDTH-1:0]     operand_x;
    logic [P_WIDTH-1:0]     operand_y;
    int                     sum_int;
    real                    real_val;
    state_e                 current_state;
    my_struct_t             data_packet;
    logic [P_WIDTH-1:0]     array_packed [L_DEPTH];
    logic [P_WIDTH-1:0]     array_unpacked [L_DEPTH];
    always_comb begin
        operand_x = in_a;
        operand_y = in_b;
        sum_int = operand_x + operand_y;
        real_val = $itor(sum_int) / 2.0;
        if (in_sel) begin
            out_result = operand_x * operand_y;
            operand_x = ~operand_x;
            current_state = ST_BUSY;
        end else begin
            out_result = operand_x | operand_y;
            operand_y = operand_y & 8'hF0;
            current_state = ST_IDLE;
        end
        out_result = (out_result << 1) | (|operand_x);
        data_packet.val1 = {operand_x[3:0], operand_y[3:0]};
        data_packet.val2 = {2{operand_x[7:4]}};
        data_packet.idx = sum_int;
        for (int i = 0; i < L_DEPTH; i++) begin
            array_packed[i] = operand_x + i;
            array_unpacked[i] = operand_y - i;
        end
        if (current_state == ST_BUSY && data_packet.val1 != 0) begin
            out_status = 3'b001; 
        end else if (current_state == ST_IDLE && data_packet.idx == 0) begin
            out_status = 3'b000; 
        end else if (real_val > 10.0) begin
            out_status = 3'b010; 
            current_state = ST_DONE;
        end else begin
            out_status = 3'b111; 
            current_state = ST_ERROR;
        end
    end
endmodule
module ProceduralControlLogic (
    input logic         clk,
    input logic         reset_n,
    input logic [15:0]  data_in,
    input logic [1:0]   cmd_in,
    output logic [15:0] data_out,
    output logic [3:0]  status_code
);
    logic [15:0]  reg_data_ff;
    logic [15:0]  comb_data;
    logic [15:0]  latch_data;
    logic [3:0]   internal_status;
    function automatic logic [15:0] calculate_checksum (input logic [15:0] val);
        logic [15:0] sum = 0;
        for (int i = 0; i < 16; i++) begin
            sum = sum + val[i];
        end
        return sum;
    endfunction
    task automatic update_status (input logic [3:0] new_status);
        internal_status = new_status; 
    endtask
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            reg_data_ff <= 16'h0000;
            status_code <= 4'b0000;
        end else begin
            reg_data_ff <= data_in + calculate_checksum(data_in); 
            status_code <= internal_status;
        end
    end
    always_comb begin
        comb_data = 16'hFFFF;
        internal_status = 4'b0000; 
        case (cmd_in)
            2'b00: begin 
                comb_data = data_in;
                update_status(4'b0001);
            end
            2'b01: begin 
                comb_data = data_in + 1;
                update_status(4'b0010);
            end
            2'b10: begin 
                int temp_data = data_in;
                int count = 0;
                while (temp_data > 0 && count < 10) begin
                    temp_data = temp_data - 1;
                    count++;
                end
                comb_data = temp_data;
                update_status(4'b0011);
            end
            default: begin 
                comb_data = 16'h0000;
                update_status(4'b1111);
            end
        endcase
        data_out = comb_data;
    end
    always_latch begin
        if (cmd_in == 2'b11) begin 
            latch_data = data_in;
        end
    end
endmodule
module ClassesAndAssertions (
    input logic         clk,
    input logic         rst,
    input logic         req_i,
    input logic [7:0]   data_i,
    output logic        ack_o,
    output logic [2:0]  status_o
);
    class MyTransaction;
        rand logic [7:0] payload;
        rand int         id;
        function new();
            payload = 8'h00;
            id = 0;
        endfunction
        function void set_payload(logic [7:0] val);
            this.payload = val;
        endfunction
        function logic [7:0] get_payload();
            return payload;
        endfunction
    endclass
    MyTransaction transaction_h; 
    logic [7:0] internal_data;
    logic       internal_ack;
    logic [2:0] internal_status;
    initial begin
        transaction_h = new();
    end
    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            internal_data <= 8'h00;
            internal_ack <= 1'b0;
            internal_status <= 3'b000;
            if (transaction_h != null) begin
                transaction_h.set_payload(8'h00);
            end
        end else begin
            if (req_i) begin
                internal_data <= data_i;
                internal_ack <= 1'b1;
                internal_status <= 3'b001; 
                if (transaction_h != null) begin
                    transaction_h.set_payload(data_i);
                end
            end else begin
                internal_ack <= 1'b0;
                if (internal_status == 3'b001) begin
                    internal_status <= 3'b010; 
                end
            end
        end
    end
    assign ack_o = internal_ack;
    assign status_o = internal_status;
    property req_ack_p;
        @(posedge clk) (req_i && !rst) |=> (internal_ack);
    endproperty
    assert property (req_ack_p) else $error("Assertion failed: req_i not followed by ack_o");
    property data_stable_p;
        @(posedge clk) (internal_ack && !rst) |-> ($stable(internal_data));
    endproperty
    assume property (data_stable_p);
    property status_transition_cover_p;
        @(posedge clk) (status_o == 3'b001 && !rst) |=> (status_o == 3'b010);
    endproperty
    cover property (status_transition_cover_p);
endmodule
module GenerateAndAdvanced #(
    parameter ENABLE_LOGIC_A = 1,
    parameter NUM_BLOCKS     = 2
) (
    input logic                 sel_gen,
    input logic [7:0]           addr,
    input logic [NUM_BLOCKS-1:0][15:0] data_in_gen,
    output logic [15:0]         data_out_gen
);
    typedef union packed {
        logic [15:0] word;
        logic [7:0]  byte[2];
        logic [3:0]  nibble[4];
    } data_union_t;
    data_union_t u_data;
    logic [15:0] internal_output;
    if (ENABLE_LOGIC_A) begin : logic_A_block
        localparam FACTOR_A = 2;
        always_comb begin
            internal_output = data_in_gen[0][addr[3:0]] * FACTOR_A;
            u_data.word = internal_output;
        end
    end else begin : logic_B_block
        localparam FACTOR_B = 3;
        always_comb begin
            internal_output = data_in_gen[0][addr[3:0]] + FACTOR_B;
            u_data.word = internal_output;
        end
    end
    genvar i;
    for (i = 0; i < NUM_BLOCKS; i++) begin : data_processor
        logic [15:0] processed_block_data;
        if (i == 0) begin
            always_comb processed_block_data = data_in_gen[i] + {16{sel_gen}};
        end else begin
            always_comb processed_block_data = data_in_gen[i] ^ {16{sel_gen}};
        end
        always_comb data_out_gen = (i == NUM_BLOCKS - 1) ? processed_block_data : 16'h0000;
    end
    always_comb begin
        if (sel_gen) begin
            u_data.byte[0] = addr[7:0];
            data_out_gen = u_data.word;
        end else begin
            data_out_gen = u_data.nibble[0];
        end
    end
endmodule
module ComplexParametersAndArrays #(
    parameter DATA_WIDTH = 16,
    parameter MEM_SIZE_X = 64,
    parameter MEM_SIZE_Y = 32,
    parameter MAX_VALUE  = (1 << DATA_WIDTH) - 1
) (
    input logic [$clog2(MEM_SIZE_X)-1:0] idx_in_x,
    input logic [$clog2(MEM_SIZE_Y)-1:0] idx_in_y,
    input logic [DATA_WIDTH-1:0]         val_in,
    output logic [DATA_WIDTH-1:0]        array_val_out
);
    localparam TOTAL_MEM_CELLS = MEM_SIZE_X * MEM_SIZE_Y;
    logic [DATA_WIDTH-1:0] memory_2d [MEM_SIZE_X][MEM_SIZE_Y];
    typedef logic [DATA_WIDTH-1:0] row_t [MEM_SIZE_Y];
    row_t packed_memory [MEM_SIZE_X];
    typedef enum logic [3:0] {
        ERR_NONE      = 4'h0,
        ERR_OVERFLOW  = 4'hA,
        ERR_UNDERFLOW = 4'hB,
        ERR_INVALID   = 4'hF
    } error_code_e;
    error_code_e current_error = ERR_NONE;
    always_comb begin
        memory_2d[idx_in_x][idx_in_y] = val_in;
        packed_memory[idx_in_x][idx_in_y] = val_in;
        array_val_out = memory_2d[idx_in_x][idx_in_y];
        if (val_in > MAX_VALUE - 10) begin
            current_error = ERR_OVERFLOW;
        end else if (val_in == 0 && idx_in_x == 0 && idx_in_y == 0) begin
            current_error = ERR_UNDERFLOW;
        end else begin
            current_error = ERR_NONE;
        end
        casez (idx_in_x)
            {$clog2(MEM_SIZE_X)-1{1'b1}} : array_val_out = array_val_out + 1; 
            default                      : array_val_out = array_val_out - 1;
        endcase
    end
    logic [3:0] error_out;
    assign error_out = current_error;
endmodule
