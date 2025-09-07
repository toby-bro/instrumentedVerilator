interface my_if;
    logic [7:0] data;
    logic valid;
endinterface
module VirtIfaceAssignComb (
    input logic [7:0] in_data_i,
    output logic out_valid_o
);
    virtual my_if vif_inst;
    assign vif_inst.data = in_data_i + 1;
    always_comb begin
        vif_inst.valid = (in_data_i > 4'd5);
    end
    assign out_valid_o = vif_inst.valid;
endmodule
interface data_if;
    logic [7:0] value;
    logic enable;
endinterface
module VirtIfaceAssignBlockingNonBlocking (
    input logic clk_i,
    input logic rst_ni,
    input logic [7:0] din_i,
    output logic [7:0] dout_o
);
    virtual data_if vif_data;
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            vif_data.enable <= 1'b0; 
            vif_data.value <= 8'h00; 
        end else begin
            vif_data.enable <= 1'b1; 
            vif_data.value = din_i;  
        end
    end
    assign dout_o = vif_data.value;
endmodule
interface control_if;
    logic cmd_a;
    logic cmd_b;
    logic status;
endinterface
module VirtIfaceIfElseMemberTracking (
    input logic sel_i,
    input logic cond_i,
    output logic out_o
);
    virtual control_if vif_ctrl;
    always_comb begin
        if (sel_i) begin
            vif_ctrl.cmd_a = 1'b1;
            vif_ctrl.cmd_b = 1'b0;
        end else begin
            vif_ctrl.cmd_a = 1'b0;
            vif_ctrl.cmd_b = 1'b1;
        end
        vif_ctrl.status = sel_i & cond_i;
        if (vif_ctrl.cmd_a = 1'b1) begin
        end
    end
    assign out_o = vif_ctrl.cmd_a ^ vif_ctrl.cmd_b;
endmodule
interface stream_if;
    logic [3:0] data;
    logic ready;
    logic valid;
endinterface
module VirtIfaceLoopAndFunction (
    input logic clk_i,
    input logic reset_ni,
    input logic start_i,
    input logic [3:0] max_count_i,
    output logic stream_done_o
);
    virtual stream_if vif_stream;
    integer i;
    logic local_var_unused; 
    function automatic void write_stream_data(input virtual stream_if vif, input logic [3:0] val);
        vif.data = val;
        vif.valid = 1'b1;
        vif.ready = 1'b0;
    endfunction
    always_ff @(posedge clk_i or negedge reset_ni) begin
        if (!reset_ni) begin
            vif_stream.ready <= 1'b0;
            stream_done_o <= 1'b0;
            local_var_unused <= 1'b0;
        end else if (start_i) begin
            vif_stream.ready <= 1'b1;
            stream_done_o <= 1'b0;
            local_var_unused <= 1'b1;
            for (i = 0; i < max_count_i; i = i + 1) begin
                vif_stream.data = i; 
                vif_stream.valid = 1'b1;
                write_stream_data(vif_stream, i);
                if (i == max_count_i - 1) stream_done_o <= 1'b1;
            end
        end
    end
    always_comb begin
        local_var_unused = 1'b0;
        while (vif_stream.data = 4'd0) begin 
            local_var_unused = 1'b1;
        end
    end
endmodule
module ClassInstantiationAndProceduralLogic (
    input logic trigger_i,
    output logic result_o
);
    class MyData;
        rand int value;
        function new(int v);
            value = v;
        endfunction
    endclass
    MyData data_obj_ref; 
    always_ff @(posedge trigger_i) begin 
        if (data_obj_ref == null) begin
            data_obj_ref = new(10); 
        end else begin
            data_obj_ref.value = data_obj_ref.value + 1;
        end
    end
    assign result_o = (data_obj_ref != null) ? data_obj_ref.value[0] : 1'b0;
endmodule
