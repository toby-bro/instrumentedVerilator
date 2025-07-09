module enum_first_last_mod (
    input  logic [2:0] sel_in,
    output logic [2:0] first_out,
    output logic [2:0] last_out
);
    typedef enum logic [2:0] {S0=0, S1=1, S2=2, S3=3, S4=4} e_t;
    parameter e_t BASE_VALUE  = S2;
    localparam e_t CONST_FIRST = BASE_VALUE.first;
    localparam e_t CONST_LAST  = BASE_VALUE.last;
    e_t v;
    always_comb begin
        v        = e_t'(sel_in);
        first_out = v.first;   
        last_out  = v.last;    
    end
endmodule
module enum_next_mod (
    input  logic   [2:0] cur_in,
    input  integer       cnt_in,
    output logic   [2:0] next_noarg_out,
    output logic   [2:0] next_cnt_out
);
    typedef enum logic [2:0] {N0=0, N1=1, N2=2, N3=3, N4=4} n_t;
    parameter n_t P_BASE      = N1;
    localparam n_t CONST_NEXT1 = P_BASE.next;      
    localparam n_t CONST_NEXT3 = P_BASE.next(3);   
    n_t cur;
    always_comb begin
        cur            = n_t'(cur_in);
        next_noarg_out = cur.next;          
        next_cnt_out   = cur.next(cnt_in);  
    end
endmodule
module enum_prev_mod (
    input  logic   [2:0] cur_in,
    input  integer       cnt_in,
    output logic   [2:0] prev_noarg_out,
    output logic   [2:0] prev_cnt_out
);
    typedef enum logic [2:0] {P0=0, P1=1, P2=2, P3=3, P4=4} p_t;
    parameter p_t P_BASE       = P3;
    localparam p_t CONST_PREV1 = P_BASE.prev;     
    localparam p_t CONST_PREV2 = P_BASE.prev(2);  
    p_t cur;
    always_comb begin
        cur            = p_t'(cur_in);
        prev_noarg_out = cur.prev;         
        prev_cnt_out   = cur.prev(cnt_in); 
    end
endmodule
module enum_num_mod (
    input  logic   [1:0] idx_in,
    output integer       num_out
);
    typedef enum logic [1:0] {RED=0, GREEN=1, BLUE=2} color_t;
    parameter color_t COLOR_PARAM = GREEN;
    localparam integer NUM_CONST  = COLOR_PARAM.num;
    color_t col;
    always_comb begin
        col     = color_t'(idx_in);
        num_out = col.num;
    end
endmodule
module enum_name_mod (
    input  logic  [1:0] state_in,
    output string       name_out
);
    typedef enum logic [1:0] {IDLE_N=0, WORK_N=1, DONE_N=2} state_t;
    parameter state_t STATE_PARAM = WORK_N;
    localparam string NAME_CONST  = STATE_PARAM.name;
    state_t st;
    always_comb begin
        st       = state_t'(state_in);
        name_out = st.name;
    end
endmodule
