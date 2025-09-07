module SimpleShadowVar_Module (
    input logic clk,
    input logic [7:0] s_in,
    output logic [7:0] s_out
);
    always_ff @(posedge clk) begin
        s_out <= s_in;
    end
endmodule
module MixedAssignMasked_Module (
    input logic clk,
    input logic [7:0] blk_comb_in,
    input logic [7:0] blk_ff_in,
    input logic [7:0] nb_ff_in,
    output logic [7:0] masked_out
);
    always_comb begin
        masked_out[3:0] = blk_comb_in[3:0];
    end
    always_ff @(posedge clk) begin
        masked_out[7:4] = blk_ff_in[3:0];
        masked_out[5:2] <= nb_ff_in[3:0];
    end
endmodule
module UnpackedArraySharedFlag_Module (
    input logic clk,
    input logic [7:0] ua_in [1:0],
    output logic [7:0] ua_out [1:0]
);
    always_ff @(posedge clk) begin
        ua_out[0] <= ua_in[0];
        ua_out[1] <= ua_in[1]; 
    end
endmodule
module ForkJoinNoneUniqueFlag_Module (
    input logic fu_in,
    output logic fu_out
);
    always_comb begin
        fork
            fu_out <= fu_in;
        join_none
    end
endmodule
module WhileLoopValueQueueWhole_Module (
    input logic clk,
    input logic [7:0] vqw_in [3:0],
    output logic [7:0] vqw_arr [3:0]
);
    always_ff @(posedge cllk) begin
        int i;
        for (i = 0; i < 4; i++) begin
            vqw_arr[i] <= vqw_in[i];
        end
    end
endmodule
module WhileLoopValueQueuePartial_Module (
    input logic clk,
    input logic [7:0] vqp_in [3:0],
    output logic [15:0] vqp_arr [3:0]
);
    always_ff @(posedge clk) begin
        int i;
        for (i = 0; i < 4; i++) begin
            vqp_arr[i][(i*2)+7 : (i*2)] <= vqp_in[i];
        end
    end
endmodule
module NonPackedMixedAssign_Module (
    input logic clk,
    input real r_in_blocking,
    input real r_in_nonblocking,
    output real r_out
);
    always_comb begin
        r_out = r_in_blocking;
    end
    always_ff @(posedge clk) begin
        r_out <= r_in_nonblocking;
    end
endmodule
