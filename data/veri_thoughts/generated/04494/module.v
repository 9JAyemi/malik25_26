
module clock_gate (
  input CLK, EN, TE,
  output ENCLK
);

  wire gated_clk;
  reg ENCLK_reg; // Declare ENCLK_reg as a register

  // Gating logic
  assign gated_clk = (TE) ? CLK : (EN) ? CLK : 1'b0;

  // D flip-flop with enable
  always @(posedge CLK) begin
    if (EN) begin
      ENCLK_reg <= gated_clk; // Use ENCLK_reg as the l-value
    end
  end

  // Output assignment
  assign ENCLK = ENCLK_reg;

endmodule
