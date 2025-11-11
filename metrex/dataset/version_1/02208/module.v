
module d_ff_en_gated (
  input CLK,
  input EN,
  input TE,
  output reg ENCLK
);

  reg ENCLK_internal = 0; // Initialize to 0 
  always @ (posedge CLK) 
    if (EN) 
      ENCLK_internal <= TE;
    else 
      ENCLK_internal <= 0;

  always @*
    ENCLK = ENCLK_internal;

endmodule