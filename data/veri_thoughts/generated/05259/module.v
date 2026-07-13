module clock_gating_cell (
  input clk,
  input en,
  output gated_clk
);

  wire and_gate_output;
  assign and_gate_output = clk & en;
  
  assign gated_clk = ~and_gate_output;

endmodule