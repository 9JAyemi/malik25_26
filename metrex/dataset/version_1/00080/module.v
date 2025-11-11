module OSERDESE2 ( 
   OFB, OQ, SHIFTOUT1, SHIFTOUT2, TBYTEOUT, TFB, TQ,
   CLK, CLKDIV, D1, D2, D3, D4, D5, D6, D7, D8, OCE, RST, SHIFTIN1,
   SHIFTIN2, T1, T2, T3, T4, TBYTEIN, TCE
   );

   parameter DATA_RATE_OQ=0;
   parameter DATA_RATE_TQ=0;
   parameter DATA_WIDTH=0;
   parameter INIT_OQ=0;
   parameter INIT_TQ=0;
   parameter SERDES_MODE=0;
   parameter SRVAL_OQ=0;
   parameter SRVAL_TQ=0;
   parameter TBYTE_CTL=0;
   parameter TBYTE_SRC=0;
   parameter TRISTATE_WIDTH=0;

     
   output OFB;                    output OQ;                     output SHIFTOUT1;              output SHIFTOUT2;              output TBYTEOUT;               output TFB;                    output TQ;                     input  CLK;                    input  CLKDIV;                 input  D1;                     input  D2;                     input  D3;                     input  D4;                     input  D5;                     input  D6;                     input  D7;                     input  D8;                     input  OCE;                    input  RST;                    input  SHIFTIN1;               input  SHIFTIN2;               input  T1;                     input  T2;                     input  T3;                     input  T4;                     input  TBYTEIN;                input  TCE;                    reg [2:0] state;


   reg [7:0] buffer;
   reg [1:0] clkdiv_sample;
   reg [3:0] even;
   reg [3:0] odd;
   
   always @ (posedge CLKDIV)
     buffer[7:0]<={D8,D7,D6,D5,D4,D3,D2,D1};
   
   always @ (negedge CLK)
     clkdiv_sample[1:0] <= {clkdiv_sample[0],CLKDIV};

   wire      load_parallel = (clkdiv_sample[1:0]==2'b00);

   always @ (negedge CLK)
     if(load_parallel)
       even[3:0]<={buffer[6],buffer[4],buffer[2],buffer[0]};
     else
       even[3:0]<={1'b0,even[3:1]};

   always @ (negedge CLK)
     if(load_parallel)
       odd[3:0]<={buffer[7],buffer[5],buffer[3],buffer[1]};
     else
       odd[3:0]<={1'b0,odd[3:1]};
     
   assign OQ = CLK ? even[0] : odd[0];
   
   assign OFB       = 1'b0;
   assign TQ        = 1'b0;
   assign TBYTEOUT  = 1'b0;
   assign SHIFTOUT1 = 1'b0;   		      
   assign SHIFTOUT2 = 1'b0;   
   assign TFB       = 1'b0;
   
endmodule 