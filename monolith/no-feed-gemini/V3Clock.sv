class MyDummyClass;
    int m_val;
    function new(int init_val);
        m_val = init_val;
    endfunction
endclass
module ClockedRegister (
    input logic clk,
    input logic rst_n,
    input logic [7:0] data_in,
    output logic [7:0] data_out
);
    logic [7:0] reg_val;
    logic [7:0] next_reg_val_comb;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            reg_val <= 8'h00;
        end else begin
            reg_val <= data_in;
        end
    end
    always_ff @(posedge clk or negedge rst_n) begin
        data_out <= reg_val;
    end
    always_comb begin
        next_reg_val_comb = data_in + 1; 
    end
endmodule
module ToggleCoverageTest (
    input logic clk_i,
    input logic [3:0] enable_i,
    output logic [3:0] out_o
);
    logic [3:0] counter_r;
    always_ff @(posedge clk_i) begin
        if (enable_i[0]) begin
            counter_r <= counter_r + 1;
        end else begin
            counter_r <= 4'b0000;
        end
    end
    assign out_o = counter_r;
    covergroup cg_toggle_en @(posedge clk_i);
        toggle_enable_cp : coverpoint enable_i {
            bins all_zeros = (enable_i == 4'b0000);
            bins all_ones  = (enable_i == 4'b1111);
        }
        toggle_out_cp : coverpoint out_o {
            bins zero = (out_o == 4'b0000);
            bins one = (out_o == 4'b0001);
            bins max_val = (out_o == 4'b1111);
        }
    endgroup
    cg_toggle_en cg_inst = new(); 
endmodule
module ComplexSequential (
    input bit clk,
    input bit reset,
    input int unsigned  operand_a,
    input int unsigned  operand_b,
    output int unsigned result_sum,
    output bit result_overflow
);
    int unsigned reg_sum;
    bit reg_overflow;
    logic [1:0] state;
    always_ff @(posedge clk) begin
        if (reset) begin
            reg_sum <= 0;
            reg_overflow <= 0;
            state <= 2'b00;
        end else begin
            reg_sum <= operand_a + operand_b;
            if (operand_a > ($bits(operand_a)'(32'hFFFF_FFFF) - operand_b)) begin
                reg_overflow <= 1;
            end else begin
                reg_overflow <= 0;
            end
            state <= state + 1; 
        end
    end
    assign result_sum = reg_sum;
    assign result_overflow = reg_overflow;
endmodule
module ParameterizedLogic (
    input logic p_clk,
    input logic [WIDTH-1:0] p_data_in,
    output logic [WIDTH-1:0] p_data_out
);
    parameter WIDTH = 8; 
    logic [WIDTH-1:0] p_reg_val;
    always_ff @(posedge p_clk) begin
        p_reg_val <= p_data_in;
    end
    assign p_data_out = p_reg_val;
endmodule
module SimpleLatch (
    input logic d_in,
    input logic en_in,
    output logic q_out
);
    logic latch_q;
    always_latch begin
        if (en_in) begin
            latch_q <= d_in;
        end
    end
    assign q_out = latch_q;
endmodule
module ConditionalActive (
    input logic clk_in,
    input logic cond_in,
    input logic data_in_a,
    input logic data_in_b,
    output logic out_reg_a,
    output logic out_reg_b
);
    logic internal_reg_a;
    logic internal_reg_b;
    always_ff @(posedge clk_in) begin
        if (cond_in) begin
            internal_reg_a <= data_in_a;
        end else begin
            internal_reg_a <= 1'b0; 
        end
    end
    always_ff @(posedge clk_in) begin
        internal_reg_b <= data_in_b;
    end
    assign out_reg_a = internal_reg_a;
    assign out_reg_b = internal_reg_b;
endmodule
module ClassInstantiationTest (
    input logic clk_inst,
    output logic [7:0] data_from_class_o
);
    MyDummyClass my_obj_inst;
    logic [7:0] internal_data_reg;
    initial begin
        my_obj_inst = new(255); 
        internal_data_reg = my_obj_inst.m_val;
    end
    always_ff @(posedge clk_inst) begin
        data_from_class_o <= internal_data_reg; 
    end
endmodule
