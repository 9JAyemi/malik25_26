
`ifdef BSV_ASSIGNMENT_DELAY
`else
`define BSV_ASSIGNMENT_DELAY
`endif

module ResetEither(A_RST,
                   B_RST,
                   RST_OUT
                  ) ;

   input            A_RST;
   input            B_RST;

   output           RST_OUT;

   assign RST_OUT = A_RST & B_RST ;

endmodule                
