module tristate_conditional (
    input  logic ctrl,
    inout  wire  tri_sig,
    output logic read_val
);
    assign tri_sig  = ctrl ? 1'bz : 1'b0;
    assign read_val = tri_sig;
endmodule
module pull_resistor_example (
    input  logic drive_low,
    inout  wire  pin,
    output logic pin_state
);
    pullup (pin);                 
    assign pin       = drive_low ? 1'b0 : 1'bz;   
    assign pin_state = pin;
endmodule
module bufif1_example (
    input  logic data_in,
    input  logic enable,
    inout  wire  line,
    output logic line_state
);
    bufif1 u_buf (line, data_in, enable);
    assign line_state = line;
endmodule
module bufif0_example (
    input  logic data_in,
    input  logic enable_n,
    inout  wire  line,
    output logic line_state
);
    bufif0 u_buf (line, data_in, enable_n);
    assign line_state = line;
endmodule
module strength_net_example (
    input  logic src_sig,
    output logic dst_sig
);
    wand net_wand;                               
    assign (strong0, strong1) net_wand = src_sig;  
    assign (weak0  , weak1  ) net_wand = 1'b0;     
    assign dst_sig = net_wand;
endmodule
module wor_z_example (
    input  logic drive_en,
    output logic result
);
    wor net_wor;
    assign (strong0, strong1) net_wor = drive_en ? 1'b1 : 1'bz; 
    assign (weak0  , weak1  ) net_wor = 1'b0;                   
    assign result = net_wor;
endmodule
module case_eq_z_example (
    input  logic [2:0] value,
    output logic       match_z
);
    assign match_z = (value === 3'b1z0);
endmodule
module concat_slice_tri (
    input  logic        select,
    inout  wire  [3:0]  tri_bus,
    output logic [7:0]  concat_out
);
    assign tri_bus   = select ? 4'hZ : 4'hA;                    
    assign concat_out = {tri_bus[3:2], 2'b00, tri_bus[1:0], 2'b11};
endmodule
