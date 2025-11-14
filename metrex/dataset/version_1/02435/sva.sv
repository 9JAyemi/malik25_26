// SVA for signal_combiner
module signal_combiner_sva (
  input A1, input A2, input B1, input B2, input C1,
  input Y,
  input VPWR, input VGND
);
  wire pwr_good = (VPWR === 1'b1) && (VGND === 1'b0);

  default clocking cb @(posedge $global_clock); endclocking
  default disable iff (!pwr_good);

  // Functional correctness when inputs are known
  assert property ((!$isunknown({A1,A2,B1,B2,C1})) |-> (Y === ((A1 & A2) | (B1 & B2) | C1)));

  // Output never X/Z when inputs known
  assert property ((!$isunknown({A1,A2,B1,B2,C1})) |-> !$isunknown(Y));

  // Dominance: any asserted term forces Y=1
  assert property (C1 |-> (Y === 1'b1));
  assert property ((A1 && A2) |-> (Y === 1'b1));
  assert property ((B1 && B2) |-> (Y === 1'b1));

  // No term true -> Y=0
  assert property ((!C1 && !(A1 && A2) && !(B1 && B2)) |-> (Y === 1'b0));

  // Stability: if inputs stable, Y stable
  assert property ($stable({A1,A2,B1,B2,C1}) |-> $stable(Y));

  // Optional: enforce valid power rails (uncomment if required)
  // assert property (pwr_good throughout 1[*]); 

  // Coverage: each term drives Y, zero case, both pairs, edges
  cover property (C1 && !(A1 && A2) && !(B1 && B2) && (Y === 1'b1));
  cover property (!C1 && (A1 && A2) && !(B1 && B2) && (Y === 1'b1));
  cover property (!C1 && !(A1 && A2) && (B1 && B2) && (Y === 1'b1));
  cover property (!C1 && !(A1 && A2) && !(B1 && B2) && (Y === 1'b0));
  cover property ((A1 && A2) && (B1 && B2) && (Y === 1'b1));
  cover property ($rose(Y));
  cover property ($fell(Y));
endmodule

bind signal_combiner signal_combiner_sva sva_i (.*);