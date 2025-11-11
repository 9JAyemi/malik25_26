
`ifdef BSV_ASSIGNMENT_DELAY
`else
`define BSV_ASSIGNMENT_DELAY
`endif

module ResetInverter(RESET_IN, RESET_OUT);

   input     RESET_IN;            output    RESET_OUT;           wire      RESET_OUT;
   
   assign    RESET_OUT = ! RESET_IN ;
   
endmodule 