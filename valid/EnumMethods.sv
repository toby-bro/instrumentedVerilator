module enum_first_last_example(
    input  logic [1:0] d_in,
    output logic [1:0] first_val,
    output logic [1:0] last_val
);
    typedef enum logic [1:0] {
        S0 = 2'd0,
        S1 = 2'd1,
        S2 = 2'd2,
        S3 = 2'd3
    } enum4_t;
    enum4_t e;
    always_comb begin
        e         = enum4_t'(d_in);
        first_val = e.first();
        last_val  = e.last();
    end
endmodule
module enum_next_prev_example(
    input  logic [2:0] in_data,
    output logic [2:0] next_val,
    output logic [2:0] prev_val
);
    typedef enum logic [2:0] {
        EA = 3'd0, EB = 3'd1, EC = 3'd2, ED = 3'd3,
        EE = 3'd4, EF = 3'd5, EG = 3'd6, EH = 3'd7
    } enum8_t;
    enum8_t ev;
    always_comb begin
        ev       = enum8_t'(in_data);
        next_val = ev.next(3);
        prev_val = ev.prev();
    end
endmodule
module enum_num_example(
    input  logic dummy_in,
    output logic [31:0] num_values
);
    typedef enum {
        RED, GREEN, BLUE, YELLOW, ORANGE, PURPLE, CYAN
    } color_t;
    color_t c;
    always_comb begin
        c = RED;
        num_values = c.num() + c.first() + {31'b0, dummy_in};
    end
endmodule
module enum_name_example(
    input  logic [2:0] state_in,
    output logic       is_done
);
    typedef enum logic [2:0] {
        ST_IDLE  = 3'd0,
        ST_RUN   = 3'd1,
        ST_DONE  = 3'd2,
        ST_ERR   = 3'd3,
        ST_WAIT  = 3'd4,
        ST_HALT  = 3'd5,
        ST_RST   = 3'd6,
        ST_PAUSE = 3'd7
    } state_t;
    state_t state_reg;
    string  cur_name;
    always_comb begin
        state_reg = state_t'(state_in);
        cur_name  = state_reg.name();
        is_done   = (cur_name == "ST_DONE");
    end
endmodule
