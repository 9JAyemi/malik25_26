// SVA for BLOCK1A
module BLOCK1A_sva (
  input logic PIN2,
  input logic GIN1,
  input logic GIN2,
  input logic PHI,
  input logic GOUT
);

  default clocking cb @(posedge PHI); endclocking

  // Functional correctness at each clock edge (compare after design updates)
  assert property (##0 (GOUT == ~ (GIN2 & (PIN2 | GIN1))));

  // Known/clean sampling at the clock edge
  assert property (!$isunknown({PIN2, GIN1, GIN2}));
  assert property (##0 !$isunknown(GOUT));

  // GOUT changes only on PHI posedge (no glitches)
  assert property (@(posedge GOUT)  $rose(PHI));
  assert property (@(negedge GOUT)  $rose(PHI));

  // Minimal but meaningful functional coverage
  // Observe both output values
  cover property (##0 (GOUT == 1'b0));
  cover property (##0 (GOUT == 1'b1));

  // Observe both output transitions at clock edges
  cover property (##0 $rose(GOUT));
  cover property (##0 $fell(GOUT));

  // Cover key truth-table partitions
  cover property ((GIN2 == 1'b0) ##0 (GOUT == 1'b1));                           // inner AND=0 due to GIN2=0
  cover property ((GIN2 == 1'b1 && (PIN2 | GIN1) == 1'b1) ##0 (GOUT == 1'b0));   // AND=1 => output 0
  cover property ((GIN2 == 1'b1 && (PIN2 | GIN1) == 1'b0) ##0 (GOUT == 1'b1));   // AND=0 => output 1

endmodule

// Bind to DUT
bind BLOCK1A BLOCK1A_sva BLOCK1A_sva_b (.PIN2(PIN2), .GIN1(GIN1), .GIN2(GIN2), .PHI(PHI), .GOUT(GOUT));