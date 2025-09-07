interface my_interface (input bit clk);
    logic data_i;
    logic enable_i;
    logic [7:0] addr_i;
    logic [31:0] write_data_i;
    modport master (output data_i, output enable_i, output addr_i, output write_data_i, input clk);
    modport slave (input data_i, input enable_i, input addr_i, input write_data_i, input clk);
endinterface
module VirtIfaceAssignW (
    input bit clk_i,
    input bit [7:0] in_addr,
    output logic out_status_o
);
    my_interface if_inst (.clk(clk_i));
    virtual my_interface vif_master;
    assign vif_master = if_inst;
    always_comb begin
        vif_master.data_i       = clk_i;
        vif_master.enable_i     = ~clk_i;
        vif_master.addr_i       = in_addr + 1;
        vif_master.write_data_i = {24'h0, in_addr, 8'hAA};
        out_status_o = vif_master.data_i & vif_master.enable_i;
    end
endmodule
module VirtIfaceAssignPost (
    input bit clk_i,
    input bit reset_n_i,
    input bit data_in_i,
    input bit [7:0] addr_in_i,
    output logic [31:0] read_data_o
);
    my_interface if_inst (.clk(clk_i));
    virtual my_interface vif_slave;
    assign vif_slave = if_inst;
    logic internal_data_reg;
    logic [7:0] internal_addr_reg;
    always_ff @(posedge clk_i or negedge reset_n_i) begin
        if (!reset_n_i) begin
            vif_slave.data_i       <= 1'b0;
            vif_slave.enable_i     <= 1'b0;
            internal_data_reg      <= 1'b0;
            internal_addr_reg      <= 8'b0;
            vif_slave.write_data_i <= 32'b0;
        end else begin
            vif_slave.data_i       <= data_in_i;
            vif_slave.enable_i     <= 1'b1;
            vif_slave.addr_i       <= addr_in_i;
            vif_slave.write_data_i <= {24'hABCD, addr_in_i};
            internal_data_reg      <= data_in_i;
            internal_addr_reg      <= addr_in_i;
        end
    end
    logic temp_enable;
    always_comb begin
        temp_enable = !vif_slave.enable_i;
        if_inst.data_i = temp_enable;
        if_inst.enable_i = temp_enable;
    end
    assign read_data_o = {if_inst.write_data_i[7:0], internal_addr_reg, internal_data_reg};
endmodule
module VirtIfaceComplexProc (
    input bit clk_i,
    input bit reset_n_i,
    input bit [3:0] count_limit_i,
    output logic [3:0] counter_o,
    output logic [7:0] result_o
);
    my_interface if_main (.clk(clk_i));
    virtual my_interface vif_complex;
    assign vif_complex = if_main;
    logic [3:0] counter_reg;
    logic [7:0] current_val_reg;
    logic [3:0] i_loop;
    always_ff @(posedge clk_i or negedge reset_n_i) begin : main_proc_block
        if (!reset_n_i) begin
            counter_reg     <= 4'b0;
            current_val_reg <= 8'b0;
            vif_complex.data_i       <= 1'b0;
            vif_complex.enable_i     <= 1'b0;
            vif_complex.addr_i       <= 8'b0;
            vif_complex.write_data_i <= 32'b0;
        end else begin
            vif_complex.data_i       <= 1'b1;
            vif_complex.enable_i     <= 1'b1;
            if (counter_reg % 2 == 0) begin
                vif_complex.addr_i <= counter_reg;
                current_val_reg    <= current_val_reg + 1;
            end else begin
                vif_complex.addr_i <= 8'hFF - counter_reg;
                current_val_reg    <= current_val_reg - 1;
            end
            i_loop = 4'b0;
            while (i_loop < count_limit_i) begin
                vif_complex.write_data_i[i_loop] <= 1'b1;
                i_loop++;
                if (i_loop == 2) begin
                    vif_complex.enable_i <= 1'b0;
                    break;
                end
            end
            counter_reg <= counter_reg + 1;
        end
    end
    task set_vif_signals (input logic new_data, input logic new_enable);
        vif_complex.data_i = new_data;
        vif_complex.enable_i = new_enable;
        vif_complex.addr_i = {4'b0, new_data, new_enable, 2'b0};
    endtask
    always_comb begin
        set_vif_signals(vif_complex.data_i ^ 1'b1, vif_complex.enable_i);
    end
    assign counter_o = counter_reg;
    assign result_o = current_val_reg;
endmodule
module VirtIfaceMemberTracking (
    input bit clk_i,
    input bit [1:0] sel_i,
    input bit data_in_i,
    output logic [31:0] debug_out
);
    my_interface if_debug (.clk(clk_i));
    virtual my_interface vif_debug;
    assign vif_debug = if_debug;
    logic [31:0] internal_reg;
    always_ff @(posedge clk_i) begin
        case (sel_i)
            2'b00: begin
                vif_debug.data_i       <= data_in_i;
                vif_debug.enable_i     <= ~data_in_i;
                vif_debug.addr_i       <= 8'h11;
                vif_debug.write_data_i <= 32'hAAAA_BBBB;
            end
            2'b01: begin
                vif_debug.data_i <= ~data_in_i;
                vif_debug.data_i <= data_in_i;
                vif_debug.enable_i <= 1'b0;
            end
            2'b10: begin
                vif_debug.addr_i       <= 8'hAA;
                vif_debug.write_data_i <= 32'hFEED_F00D;
                vif_debug.data_i       <= 1'b1;
                vif_debug.addr_i       <= 8'hCC;
            end
            default: begin
                vif_debug.data_i       <= 1'b0;
                vif_debug.enable_i     <= 1'b0;
                vif_debug.addr_i       <= 8'b0;
                vif_debug.write_data_i <= 32'b0;
            end
        endcase
        internal_reg <= {vif_debug.data_i, vif_debug.enable_i, vif_debug.addr_i, vif_debug.write_data_i};
    end
    assign debug_out = internal_reg;
endmodule
