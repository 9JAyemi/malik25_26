
`ifdef BSV_ASSIGNMENT_DELAY
`else
`define BSV_ASSIGNMENT_DELAY
`endif

`ifdef BSV_POSITIVE_RESET
  `define BSV_RESET_VALUE 1'b1
  `define BSV_RESET_EDGE posedge
`else
  `define BSV_RESET_VALUE 1'b0
  `define BSV_RESET_EDGE negedge
`endif



module ResetEither(A_RST,
                   B_RST,
                   RST_OUT
                  ) ;

   input            A_RST;
   input            B_RST;

   output           RST_OUT;

   assign RST_OUT = ((A_RST == `BSV_RESET_VALUE) || (B_RST == `BSV_RESET_VALUE)) ? `BSV_RESET_VALUE : ~ `BSV_RESET_VALUE;

endmodule
