
module and_module (
                   // Outputs
                   o_bus,
                   // Inputs
                   i_bus1,
                   i_bus2
                   );

   input  [7:0]  i_bus1 ;
   input  [7:0]  i_bus2 ;
   output wire [7:0] o_bus ;

   assign o_bus = (i_bus1 & i_bus2);

endmodule
