module clock_gating_cell (
  input clk,
  input enable,
  output gated_clk
);

  assign gated_clk = enable ? clk : 1'b0;

endmodule