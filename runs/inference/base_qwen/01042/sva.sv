module DFF_AR_assertions (
  input logic CLK,
  input logic RST,
  input logic D,
  output logic Q,
  output logic QN
);
  // Reset behavior: Q and QN should be 0 and 1 respectively when RST is active
  reset: assert property (
    @(posedge CLK) disable iff (!RST) (Q == 1'b0) && (QN == 1'b1)
  );

  // DFF behavior: Q should be equal to D and QN should be the inverse of D when RST is inactive
  dff_behavior: assert property (
    @(posedge CLK) disable iff (RST) (Q == D) && (QN == ~D)
  );
endmodule