module idelay_ctrl_rdy_module (
   input  clk200,
   input  rst200,
   output idelay_ctrl_rdy
   );

   wire idelay_ctrl_rdy_x0y5;
   wire idelay_ctrl_rdy_x0y6;

  IDELAYCTRL  u_idelayctrl_x0y5
    (
     .RDY(idelay_ctrl_rdy_x0y5),
     .REFCLK(clk200),
     .RST(rst200)
    );

  IDELAYCTRL u_idelayctrl_x0y6
    (
     .RDY(idelay_ctrl_rdy_x0y6),
     .REFCLK(clk200),
     .RST(rst200)
    );

   assign idelay_ctrl_rdy = idelay_ctrl_rdy_x0y5 & idelay_ctrl_rdy_x0y6;

endmodule 
module IDELAYCTRL (
   input  REFCLK,
   input  RST,
   output RDY
   );

   reg delay_rdy;

   always @ (posedge REFCLK or posedge RST) begin
      if (RST) begin
         delay_rdy <= 1'b0;
      end else begin
         delay_rdy <= 1'b1;
      end
   end

   assign RDY = delay_rdy;

endmodule