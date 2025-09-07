module pre_inc_expr_mod(
    input  logic         clk,
    input  logic [7:0]   in_data,
    output logic [7:0]   out_data
);
    logic [7:0] counter;
    always_ff @(posedge clk) begin
        if (in_data[0]) counter <= 8'd0;
        out_data <= ++counter;          
    end
endmodule
module post_inc_expr_mod(
    input  logic         clk,
    input  logic [7:0]   in_data,
    output logic [7:0]   out_data
);
    logic [7:0] counter;
    always_ff @(posedge clk) begin
        if (in_data[1]) counter <= 8'd0;
        out_data <= counter++;          
    end
endmodule
module pre_dec_stmt_mod(
    input  logic         clk,
    input  logic [3:0]   ctrl,
    output logic [7:0]   out_val
);
    logic [7:0] value;
    always_ff @(posedge clk) begin
        if (ctrl[0]) value <= 8'd15;
        --value;                        
        out_val <= value;
    end
endmodule
module array_sel_inc_mod(
    input  logic         clk,
    input  logic [7:0]   in_byte,
    output logic [7:0]   array_out
);
    logic [7:0]        mem   [0:15];
    logic [3:0]        index;
    always_ff @(posedge clk) begin
        mem[index] <= in_byte;
        mem[index++]++;                
        array_out <= mem[index];
    end
endmodule
module loop_inc_mod(
    input  logic         clk,
    input  logic [7:0]   din,
    output logic [7:0]   dout
);
    logic [3:0] idx;
    logic [7:0] sum;
    logic [7:0] vect [0:7];
    always_ff @(posedge clk) begin
        idx  <= 0;
        sum  <= 0;
        foreach (vect[i]) begin
            vect[i] <= din + i;
        end
        while (idx++ < 8) begin        
            sum <= sum + vect[idx-1];
        end
        dout <= sum;
    end
endmodule
module task_func_inc_mod(
    input  logic         clk,
    input  logic [7:0]   data_in,
    output logic [7:0]   data_out
);
    logic [7:0] state;
    function automatic logic [7:0] update_val(input logic [7:0] val);
        automatic logic [7:0] tmp;
        tmp = val;
        tmp++;                         
        update_val = ++tmp;            
    endfunction
    task automatic adjust_state(ref logic [7:0] s);
        s++;                           
        --s;                           
    endtask
    always_ff @(posedge clk) begin
        state <= update_val(data_in);
        adjust_state(state);
        data_out <= state;
    end
endmodule
