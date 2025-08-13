module wide_ops_mod (
    input  logic [299:0] in_a,
    output logic [299:0] out_y
);
    localparam logic [299:0] BIG_CONST =
        300'h0123456789ABCDEF0123456789ABCDEF0123456789ABCDEF0123456789ABCDEF;
    always_comb begin
        out_y = in_a + BIG_CONST;
    end
endmodule
module shift_fix_mod (
    input  logic [31:0] in_val,
    input  logic [5:0]  shift_amt,
    output logic [31:0] out_shift_l,
    output logic [31:0] out_shift_r
);
    assign out_shift_l = in_val << shift_amt;
    assign out_shift_r = in_val >> shift_amt;
endmodule
module while_counter_mod (
    input  logic        clk,
    input  logic        rst_n,
    input  logic [7:0]  in_val,
    output logic [7:0]  out_count
);
    logic [7:0] counter;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) counter <= 8'h0;
        else begin
            int i;
            i = in_val;
            while (i > 0) begin
                i = i - 1;
                counter <= counter + 1;
            end
        end
    end
    assign out_count = counter;
endmodule
module cond_sel_mod (
    input  logic [15:0] a,
    input  logic [15:0] b,
    input  logic [15:0] c,
    input  logic [15:0] d,
    input  logic [3:0]  idx,
    output logic [15:0] y
);
    always_comb begin
        y = ((a + b) > (c + d))
                ? {15'b0, a[idx]}        
                : {15'b0, b[idx]};       
    end
endmodule
module string_format_mod (
    input  logic [31:0] in_val,
    output logic [31:0] str_len
);
    string s;
    always_comb begin
        s       = $sformatf("VALUE=%0d", in_val);
        str_len = s.len();
    end
endmodule
module array_pack_conv_mod (
    input  logic [31:0] in_packed,
    output logic [31:0] out_packed
);
    logic [3:0][7:0] unpacked_array;   
    always_comb begin
        unpacked_array = in_packed;    
        out_packed     = unpacked_array; 
    end
endmodule
module queue_conversion_mod (
    input  logic [7:0] in_data0,
    input  logic [7:0] in_data1,
    input  logic [7:0] in_data2,
    input  logic [7:0] in_data3,
    output logic [7:0] out_data
);
    logic [7:0] fixed_arr [0:3];
    logic [7:0] queue_data [$];
    always_comb begin
        fixed_arr[0] = in_data0;
        fixed_arr[1] = in_data1;
        fixed_arr[2] = in_data2;
        fixed_arr[3] = in_data3;
        queue_data   = fixed_arr;              
        if (queue_data.size() != 0)
            out_data = queue_data[0];
        else
            out_data = 8'h00;
    end
endmodule
module random_generator_mod (
    input  logic [31:0] seed,
    output logic [31:0] random_val
);
    always_comb begin
        random_val = $urandom(seed);
    end
endmodule
class Multiplier;
    int factor;
    function new (int f);
        factor = f;
    endfunction
    function int apply (int v);
        return v * factor;
    endfunction
endclass
module class_inst_mod (
    input  logic [15:0] in_val,
    output logic [15:0] out_val
);
    always_comb begin
        automatic Multiplier m = new(2);
        out_val = m.apply(in_val);
    end
endmodule
module array_sel_mod (
    input  logic [7:0] in0,
    input  logic [7:0] in1,
    input  logic [7:0] in2,
    input  logic [7:0] in3,
    input  logic [1:0] sel,
    output logic [7:0] dout
);
    logic [7:0] arr [0:3];
    always_comb begin
        arr[0] = in0;
        arr[1] = in1;
        arr[2] = in2;
        arr[3] = in3;
        dout   = arr[sel];            
    end
endmodule
module assoc_sel_mod (
    input  logic [31:0] in_val,
    output logic [31:0] out_val
);
    typedef int int_assoc_t [string];
    int_assoc_t aa;
    string key;
    always_comb begin
        key       = "default";
        aa[key]   = in_val;
        out_val   = aa[key];          
    end
endmodule
