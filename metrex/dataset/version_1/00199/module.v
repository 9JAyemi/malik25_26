

module SYM_GEN_4BYTE
(
    GEN_SCP,
    GEN_ECP,
    GEN_PAD,
    TX_PE_DATA,
    TX_PE_DATA_V,
    GEN_CC,


    GEN_A,
    GEN_K,
    GEN_R,
    GEN_V,


    GEN_SP,
    GEN_SPA,


    TX_CHAR_IS_K,
    TX_DATA,


    USER_CLK
);
`define DLY #1

input   [0:1]   GEN_SCP;        input   [0:1]   GEN_ECP;        input   [0:1]   GEN_PAD;        input   [0:31]  TX_PE_DATA;     input   [0:1]   TX_PE_DATA_V;   input           GEN_CC;         input           GEN_A;          input   [0:3]   GEN_K;          input   [0:3]   GEN_R;          input   [0:3]   GEN_V;          input           GEN_SP;         input           GEN_SPA;        output  [3:0]   TX_CHAR_IS_K;   output  [31:0]  TX_DATA;        input           USER_CLK;       reg     [31:0]  TX_DATA;
    reg     [3:0]   TX_CHAR_IS_K;


reg     [0:1]   gen_scp_r;
    reg     [0:1]   gen_ecp_r;
    reg     [0:1]   gen_pad_r;
    reg     [0:31]  tx_pe_data_r;
    reg     [0:1]   tx_pe_data_v_r;
    reg             gen_cc_r;
    reg             gen_a_r;
    reg     [0:3]   gen_k_r;
    reg     [0:3]   gen_r_r;
    reg     [0:3]   gen_v_r;
    reg             gen_sp_r;
    reg             gen_spa_r;


wire    [0:3]   idle_c;

always @(posedge USER_CLK)
    begin
        gen_scp_r       <=  `DLY    GEN_SCP;
        gen_ecp_r       <=  `DLY    GEN_ECP;
        gen_pad_r       <=  `DLY    GEN_PAD;
        tx_pe_data_r    <=  `DLY    TX_PE_DATA;
        tx_pe_data_v_r  <=  `DLY    TX_PE_DATA_V;
        gen_cc_r        <=  `DLY    GEN_CC;
        gen_a_r         <=  `DLY    GEN_A;
        gen_k_r         <=  `DLY    GEN_K;
        gen_r_r         <=  `DLY    GEN_R;
        gen_v_r         <=  `DLY    GEN_V;
        gen_sp_r        <=  `DLY    GEN_SP;
        gen_spa_r       <=  `DLY    GEN_SPA;
    end



    assign  idle_c[0]   =   !(gen_scp_r[0]      |
                              gen_ecp_r[0]      |
                              tx_pe_data_v_r[0] |
                              gen_cc_r          |
                              gen_sp_r          |
                              gen_spa_r         |
                              gen_v_r[0]);



    always @ (posedge USER_CLK)
    begin
        if(gen_scp_r[0])            TX_DATA[31:24] <= `DLY  8'h5c;             if(gen_ecp_r[0])            TX_DATA[31:24] <= `DLY  8'hfd;             if(tx_pe_data_v_r[0])       TX_DATA[31:24] <= `DLY  tx_pe_data_r[0:7]; if(gen_cc_r)                TX_DATA[31:24] <= `DLY  8'hf7;             if(idle_c[0] & gen_a_r)     TX_DATA[31:24] <= `DLY  8'h7c;             if(idle_c[0] & gen_k_r[0])  TX_DATA[31:24] <= `DLY  8'hbc;             if(idle_c[0] & gen_r_r[0])  TX_DATA[31:24] <= `DLY  8'h1c;             if(gen_sp_r)                TX_DATA[31:24] <= `DLY  8'hbc;             if(gen_spa_r   )            TX_DATA[31:24] <= `DLY  8'hbc;             if(gen_v_r[0])              TX_DATA[31:24] <= `DLY  8'he8;             end



    always @(posedge USER_CLK)
        TX_CHAR_IS_K[3] <=  `DLY    !(tx_pe_data_v_r[0] |
                                      gen_v_r[0]);


    assign  idle_c[1]   =   !(gen_scp_r[0]      |
                              gen_ecp_r[0]      |
                              tx_pe_data_v_r[0] |
                              gen_cc_r          |
                              gen_sp_r          |
                              gen_spa_r         |
                              gen_v_r[1]);


    always @ (posedge USER_CLK)
    begin
        if(gen_scp_r[0])                      TX_DATA[23:16] <= `DLY 8'hfb;               if(gen_ecp_r[0])                      TX_DATA[23:16] <= `DLY 8'hfe;               if(tx_pe_data_v_r[0] & gen_pad_r[0])  TX_DATA[23:16] <= `DLY 8'h9c;               if(tx_pe_data_v_r[0] & !gen_pad_r[0]) TX_DATA[23:16] <= `DLY tx_pe_data_r[8:15];  if(gen_cc_r)                          TX_DATA[23:16] <= `DLY 8'hf7;               if(idle_c[1] & gen_k_r[1])            TX_DATA[23:16] <= `DLY 8'hbc;               if(idle_c[1] & gen_r_r[1])            TX_DATA[23:16] <= `DLY 8'h1c;               if(gen_sp_r)                          TX_DATA[23:16] <= `DLY 8'h4a;               if(gen_spa_r)                         TX_DATA[23:16] <= `DLY 8'h2c;               if(gen_v_r[1])                        TX_DATA[23:16] <= `DLY 8'he8;               end


    always @(posedge USER_CLK)
        TX_CHAR_IS_K[2] <= `DLY !((tx_pe_data_v_r[0] && !gen_pad_r[0]) |
                                  gen_sp_r          |
                                  gen_spa_r         |
                                  gen_v_r[1]);


    assign  idle_c[2]   =   !(gen_scp_r[1]      |
                              gen_ecp_r[1]      |
                              tx_pe_data_v_r[1] |
                              gen_cc_r          |
                              gen_sp_r          |
                              gen_spa_r         |
                              gen_v_r[2]);



    always @ (posedge USER_CLK)
    begin
        if(gen_scp_r[1])                TX_DATA[15:8] <= `DLY  8'h5c;             if(gen_ecp_r[1])                TX_DATA[15:8] <= `DLY  8'hfd;             if(tx_pe_data_v_r[1])           TX_DATA[15:8] <= `DLY  tx_pe_data_r[16:23]; if(gen_cc_r)                    TX_DATA[15:8] <= `DLY  8'hf7;             if(idle_c[2] & gen_k_r[2])      TX_DATA[15:8] <= `DLY  8'hbc;             if(idle_c[2] & gen_r_r[2])      TX_DATA[15:8] <= `DLY  8'h1c;             if(gen_sp_r)                    TX_DATA[15:8] <= `DLY  8'h4a;             if(gen_spa_r)                   TX_DATA[15:8] <= `DLY  8'h2c;             if(gen_v_r[2])                  TX_DATA[15:8] <= `DLY  8'he8;             end



    always @(posedge USER_CLK)
        TX_CHAR_IS_K[1] <=  `DLY    !(tx_pe_data_v_r[1] |
                                      gen_sp_r          |
                                      gen_spa_r         |
                                      gen_v_r[2]);


    assign  idle_c[3]   =   !(gen_scp_r[1]      |
                              gen_ecp_r[1]      |
                              tx_pe_data_v_r[1] |
                              gen_cc_r          |
                              gen_sp_r          |
                              gen_spa_r         |
                              gen_v_r[3]);



    always @ (posedge USER_CLK)
    begin
        if(gen_scp_r[1])                      TX_DATA[7:0]  <= `DLY 8'hfb;               if(gen_ecp_r[1])                      TX_DATA[7:0]  <= `DLY 8'hfe;               if(tx_pe_data_v_r[1] & gen_pad_r[1])  TX_DATA[7:0]  <= `DLY 8'h9c;               if(tx_pe_data_v_r[1] & !gen_pad_r[1]) TX_DATA[7:0]  <= `DLY tx_pe_data_r[24:31]; if(gen_cc_r)                          TX_DATA[7:0]  <= `DLY 8'hf7;               if(idle_c[3] & gen_k_r[3])            TX_DATA[7:0]  <= `DLY 8'hbc;               if(idle_c[3] & gen_r_r[3])            TX_DATA[7:0]  <= `DLY 8'h1c;               if(gen_sp_r)                          TX_DATA[7:0]  <= `DLY 8'h4a;               if(gen_spa_r)                         TX_DATA[7:0]  <= `DLY 8'h2c;               if(gen_v_r[3])                        TX_DATA[7:0]  <= `DLY 8'he8;               end



    always @(posedge USER_CLK)
        TX_CHAR_IS_K[0] <= `DLY !((tx_pe_data_v_r[1] && !gen_pad_r[1]) |
                                   gen_sp_r          |
                                   gen_spa_r         |
                                   gen_v_r[3]);

endmodule
