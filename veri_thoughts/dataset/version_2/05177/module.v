


 
module generic_baseblocks_v2_1_mux #
  (
   parameter         C_FAMILY                         = "rtl",
                       parameter integer C_SEL_WIDTH                      = 4,
                       parameter integer C_DATA_WIDTH                     = 2
                       )
  (
   input  wire [C_SEL_WIDTH-1:0]                    S,
   input  wire [(2**C_SEL_WIDTH)*C_DATA_WIDTH-1:0]  A,
   output wire [C_DATA_WIDTH-1:0]                   O
   );
  
  
  genvar bit_cnt;
  
  
  generate
    if ( C_FAMILY == "rtl" || C_SEL_WIDTH < 3 ) begin : USE_RTL
      assign O = A[(S)*C_DATA_WIDTH +: C_DATA_WIDTH];
      
    end else begin : USE_FPGA
      
      wire [C_DATA_WIDTH-1:0] C;
      wire [C_DATA_WIDTH-1:0] D;
      
      generic_baseblocks_v2_1_mux # 
      (
       .C_FAMILY      (C_FAMILY),
       .C_SEL_WIDTH   (C_SEL_WIDTH-1),
       .C_DATA_WIDTH  (C_DATA_WIDTH)
      ) mux_c_inst 
      (
       .S   (S[C_SEL_WIDTH-2:0]),
       .A   (A[(2**(C_SEL_WIDTH-1))*C_DATA_WIDTH-1 : 0]),
       .O   (C)
      ); 
      
      generic_baseblocks_v2_1_mux # 
      (
       .C_FAMILY      (C_FAMILY),
       .C_SEL_WIDTH   (C_SEL_WIDTH-1),
       .C_DATA_WIDTH  (C_DATA_WIDTH)
      ) mux_d_inst 
      (
       .S   (S[C_SEL_WIDTH-2:0]),
       .A   (A[(2**C_SEL_WIDTH)*C_DATA_WIDTH-1 : (2**(C_SEL_WIDTH-1))*C_DATA_WIDTH]),
       .O   (D)
      ); 
      
      for (bit_cnt = 0; bit_cnt < C_DATA_WIDTH ; bit_cnt = bit_cnt + 1) begin : NUM
        if ( C_SEL_WIDTH == 4 ) begin : USE_F8
        
          MUXF8 muxf8_inst 
          (
           .I0  (C[bit_cnt]),
           .I1  (D[bit_cnt]),
           .S   (S[C_SEL_WIDTH-1]),
           .O   (O[bit_cnt])
          ); 
          
        end else if ( C_SEL_WIDTH == 3 ) begin : USE_F7
      
          MUXF7 muxf7_inst 
          (
           .I0  (C[bit_cnt]),
           .I1  (D[bit_cnt]),
           .S   (S[C_SEL_WIDTH-1]),
           .O   (O[bit_cnt])
          ); 
          
        end end end
  endgenerate
  
  
endmodule
