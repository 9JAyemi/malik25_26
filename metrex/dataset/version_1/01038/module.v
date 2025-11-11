

module aurora_201_STANDARD_CC_MODULE
(
    WARN_CC,
    DO_CC,
    
    
    DCM_NOT_LOCKED,
    USER_CLK,
    CHANNEL_UP

);

`define DLY #1


output      WARN_CC;
    output      DO_CC;
    
    
    input       DCM_NOT_LOCKED;
    input       USER_CLK;
    input       CHANNEL_UP;
    
    
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



wire    start_cc_c;
    wire    inner_count_done_r;
    wire    middle_count_done_c;
    wire    cc_idle_count_done_c;
    
   
always @(posedge USER_CLK)
        count_13d_srl_r     <=  `DLY    {count_13d_flop_r, count_13d_srl_r[0:10]};
        
    
    assign  inner_count_done_r  =  count_13d_srl_r[11];
 
 
    always @(posedge USER_CLK)
        if(~CHANNEL_UP)
            count_13d_flop_r    <=  `DLY    1'b0;
        else if(CHANNEL_UP && reset_r)
            count_13d_flop_r    <=  `DLY    1'b1;
        else
            count_13d_flop_r    <=  `DLY    inner_count_done_r;
            
 
  
 
 
 
 
    always @(posedge USER_CLK)
        if(inner_count_done_r|| !CHANNEL_UP)
            count_16d_srl_r     <=  `DLY    {count_16d_flop_r, count_16d_srl_r[0:13]};
            
    
    assign  middle_count_done_c =   inner_count_done_r && count_16d_srl_r[14];     
 
 
    
    always @(posedge USER_CLK)
        if(~CHANNEL_UP)
            count_16d_flop_r    <=  `DLY    1'b0;
        else if(CHANNEL_UP && reset_r)
            count_16d_flop_r    <=  `DLY    1'b1;
        else if(inner_count_done_r)    
            count_16d_flop_r    <=  `DLY    middle_count_done_c;
 

  
 
 
    always @(posedge USER_CLK)
        if(middle_count_done_c || !CHANNEL_UP)
            count_24d_srl_r     <=  `DLY    {count_24d_flop_r, count_24d_srl_r[0:21]};
            
            
    assign  cc_idle_count_done_c    =   middle_count_done_c & count_24d_srl_r[22];
    
    always @(posedge USER_CLK)
        if(~CHANNEL_UP)
            count_24d_flop_r    <=  `DLY    1'b0;
        else if(CHANNEL_UP && reset_r)
            count_24d_flop_r    <=  `DLY    1'b1;
        else if(middle_count_done_c)
            count_24d_flop_r    <=  `DLY    cc_idle_count_done_c;   
 
    
    
    initial
        prepare_count_r = 10'b0000000000;
 
 
 
     always @(posedge USER_CLK)
         prepare_count_r <=  `DLY    {cc_idle_count_done_c,prepare_count_r[0:8]};
 

 
 
    always @(posedge USER_CLK)
         if(!CHANNEL_UP)                            WARN_CC    <=  `DLY    1'b0;
         else if(cc_idle_count_done_c)              WARN_CC    <=  `DLY    1'b1;
         else if(prepare_count_r[9])                WARN_CC    <=  `DLY    1'b0;
 


    initial
         cc_count_r = 6'b000000;
 
 
 
    always @(posedge USER_CLK)
        reset_r <=  `DLY    !CHANNEL_UP;
 
 
 
    assign start_cc_c   =   prepare_count_r[9] || (CHANNEL_UP && reset_r);
 
 
     always @(posedge USER_CLK)
         cc_count_r      <=  `DLY    {(!CHANNEL_UP|prepare_count_r[9]),cc_count_r[0:4]};
        
        
        
     always @(posedge USER_CLK)
         if(!CHANNEL_UP)                 DO_CC <=  `DLY    1'b0;
         else if(start_cc_c)             DO_CC <=  `DLY    1'b1;
         else if(cc_count_r[5])          DO_CC <=  `DLY    1'b0;         
         
endmodule


