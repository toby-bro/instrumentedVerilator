module pre_expr_inc(
    input  logic [7:0] a_in,
    output logic [7:0] y
);
    logic [7:0] a;
    always_comb begin
        a = a_in;
        y = ++a;
    end
endmodule
module post_stmt_inc(
    input  logic        clk,
    input  logic [7:0]  in,
    output logic [7:0]  out
);
    logic [7:0] reg_var;
    always @(posedge clk) begin
        reg_var <= in;
        reg_var++;          
        out     <= reg_var;
    end
endmodule
module array_sel_inc(
    input  logic        clk,
    input  logic [7:0]  din,
    output logic [7:0]  dout
);
    logic [7:0] arr [0:3];
    logic [1:0] idx_counter;
    function automatic int get_idx();
        idx_counter++;          
        get_idx = idx_counter;
    endfunction
    always @(posedge clk) begin
        arr[get_idx()]++;       
        arr[0]        <= din;
        dout          <= arr[idx_counter & 2'b11];
    end
endmodule
module while_cond_inc(
    input  logic clk,
    input  logic start,
    output logic done
);
    logic [3:0] counter;
    logic       done_r;
    always @(posedge clk) begin
        if (start) begin
            counter = 0;
            while (++counter < 4) begin
            end
            done_r = 1;
        end else begin
            done_r = 0;
        end
    end
    assign done = done_r;
endmodule
module if_cond_inc(
    input  logic [7:0] a,
    output logic       flag
);
    logic [7:0] b;
    always_comb begin
        b = a;
        if (b++)        
            flag = 1'b1;
        else
            flag = 1'b0;
    end
endmodule
module case_inc(
    input  logic [2:0] sel,
    output logic [7:0] out
);
    logic [7:0] x;
    always_comb begin
        x = 8'h0;
        unique case (sel)
            3'd0: x = 8'h1;
            3'd1: x = 8'h2;
            default: x++;   
        endcase
        out = x;
    end
endmodule
module wait_inc(
    input  logic       clk,
    input  logic       trigger,
    output logic [3:0] count
);
    logic       flag;
    logic [3:0] cnt;
    always @(posedge clk) begin
        if (trigger) begin
            flag <= 1'b0;
            cnt  <= 4'd0;
            wait (flag++);      
            cnt  <= cnt + 1;
        end
    end
    assign count = cnt;
endmodule
module task_inc(
    input  logic       clk,
    input  logic       start,
    output logic [3:0] value
);
    logic [3:0] reg_var;
    task automatic inc_task();
        reg_var++;              
    endtask
    always @(posedge clk) begin
        if (start)
            inc_task();
        value <= reg_var;
    end
endmodule
module logand_inc(
    input  logic [7:0] in1,
    output logic [7:0] out1
);
    logic [7:0] val;
    always_comb begin
        val = in1;
        if (val++ && in1[0])    
            out1 = val;
        else
            out1 = 8'h00;
    end
endmodule
module pre_dec(
    input  logic [7:0] a_in,
    output logic [7:0] y
);
    logic [7:0] a;
    always_comb begin
        a = a_in;
        y = --a;                
    end
endmodule
module post_dec_stmt(
    input  logic        clk,
    input  logic [7:0]  in,
    output logic [7:0]  out
);
    logic [7:0] reg_var;
    always @(posedge clk) begin
        reg_var <= in;
        reg_var--;              
        out     <= reg_var;
    end
endmodule
