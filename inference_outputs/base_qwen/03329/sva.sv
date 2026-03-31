```systemverilog
module clock_gate_sva (
  input logic CLK,
  input logic EN,
  input logic TE,
  input logic RST,
  output logic ENCLK
);
  // ENCLK is always LOW when RST is asserted
  reset: assert property (
    @(posedge CLK) disable iff (!RST) RST |-> (ENCLK == 1'b0)
  );

  // ENCLK is driven by EN when TE is asserted and RST is deasserted
  enable: assert property (
    @(posedge CLK) disable iff (RST) TE |-> (ENCLK == EN)
  );

  // ENCLK remains unchanged when TE is deasserted and RST is deasserted
  hold: assert property (
    @(posedge CLK) disable iff (RST) !TE |-> (ENCLK == ENCLK)
  );
endmodule
```