

module aur1_STANDARD_CC_MODULE
(
    RESET,
    WARN_CC,
    DO_CC,
    
    PLL_NOT_LOCKED,
    USER_CLK

);

`define DLY #1

output      WARN_CC;
    output      DO_CC;
    
    input       PLL_NOT_LOCKED;
    input       USER_CLK;
    input       RESET;
    
reg             WARN_CC;
    reg             DO_CC;

reg     [0:9]   prepare_count_r;
    reg     [0:5]   cc_count_r;
    reg             reset_r;
    
    reg     [0:11]  count_13d_srl_r;
    reg             count_13d_flop_r;
    reg     [0:14]  count_16d_srl_r;
    reg             count_16d_flop_r;
    reg     [0:22]  count_24d_srl_r;
    reg             count_24d_flop_r;    

wire    enable_cc_c;

    wire    start_cc_c;
    wire    inner_count_done_r;
    wire    middle_count_done_c;
    wire    cc_idle_count_done_c;
   
assign enable_cc_c = !RESET;
 
    always @(posedge USER_CLK)
       if(RESET)
        count_13d_srl_r     <=  `DLY    12'b000000000000;
       else
        count_13d_srl_r     <=  `DLY    {count_13d_flop_r, count_13d_srl_r[0:10]};
        
    assign  inner_count_done_r  =  count_13d_srl_r[11];
 
    always @(posedge USER_CLK)
        if(RESET)
            count_13d_flop_r    <=  `DLY    1'b0;
        else if(enable_cc_c && reset_r)
            count_13d_flop_r    <=  `DLY    1'b1;
        else
            count_13d_flop_r    <=  `DLY    inner_count_done_r;
 
    always @(posedge USER_CLK)
        if(RESET)
            count_16d_srl_r     <=  `DLY    15'b000000000000000;
        else if(inner_count_done_r|| !enable_cc_c)
            count_16d_srl_r     <=  `DLY    {count_16d_flop_r, count_16d_srl_r[0:13]};
            
    assign  middle_count_done_c =   inner_count_done_r && count_16d_srl_r[14];     
 
    always @(posedge USER_CLK)
        if(RESET)
            count_16d_flop_r    <=  `DLY    1'b0;
        else if(enable_cc_c && reset_r)
            count_16d_flop_r    <=  `DLY    1'b1;
        else if(inner_count_done_r)    
            count_16d_flop_r    <=  `DLY    middle_count_done_c;
 
 
    always @(posedge USER_CLK)
        if(RESET)
            count_24d_srl_r     <=  `DLY   23'b00000000000000000000000; 
        else if(middle_count_done_c || !enable_cc_c)
            count_24d_srl_r     <=  `DLY    {count_24d_flop_r, count_24d_srl_r[0:21]};
            
    assign  cc_idle_count_done_c    =   middle_count_done_c & count_24d_srl_r[22];
    
    always @(posedge USER_CLK)
        if(RESET)
            count_24d_flop_r    <=  `DLY    1'b0;
        else if(enable_cc_c && reset_r)
            count_24d_flop_r    <=  `DLY    1'b1;
        else if(middle_count_done_c)
            count_24d_flop_r    <=  `DLY    cc_idle_count_done_c;   
            
    
    initial
        prepare_count_r = 10'b0000000000;
 
     always @(posedge USER_CLK)
        if(RESET)
         prepare_count_r <=  `DLY    10'b0000000000;
        else
         prepare_count_r <=  `DLY    {6'd0,cc_idle_count_done_c,prepare_count_r[6:8]};
         
 
    always @(posedge USER_CLK)
         if(RESET)                                  WARN_CC    <=  `DLY    1'b0;
         else if(cc_idle_count_done_c)              WARN_CC    <=  `DLY    1'b1;
         else if(prepare_count_r[9])                WARN_CC    <=  `DLY    1'b0;

    initial
         cc_count_r = 6'b000000;
 
    always @(posedge USER_CLK)
        reset_r <=  `DLY    RESET;
 
    assign start_cc_c   =   prepare_count_r[9] || (enable_cc_c && reset_r);
 
 
     always @(posedge USER_CLK)
       if(RESET)
         cc_count_r      <=  `DLY   6'b000000; 
       else
         cc_count_r      <=  `DLY    {(!enable_cc_c|prepare_count_r[9]),cc_count_r[0:4]};
        
     always @(posedge USER_CLK)
         if(RESET)                       DO_CC <=  `DLY    1'b0;
         else if(start_cc_c)             DO_CC <=  `DLY    1'b1;
         else if(cc_count_r)             DO_CC <=  `DLY    1'b1;         
         else                            DO_CC <=  `DLY    1'b0;         
         

endmodule
