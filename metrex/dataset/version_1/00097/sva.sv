// SVA for sky130_fd_sc_hd__a21oi
// Function: Y = ~(B1 | (A1 & A2))

module sky130_fd_sc_hd__a21oi_sva (
  input logic A1,
  input logic A2,
  input logic B1,
  input logic Y
);
  // Sample on any change of signals
  default clocking cb @(*) ; endclocking

  // Functional correctness when inputs are known
  assert property (!$isunknown({A1,A2,B1}) |-> (Y === ~(B1 | (A1 & A2))))
    else $error("A21OI mismatch: Y=%b expected=%b (A1=%b A2=%b B1=%b)",
                Y, ~(B1 | (A1 & A2)), A1, A2, B1);

  // Optional sanity: if all known, Y must be 2-state (redundant with above but clearer intent)
  assert property (!$isunknown({A1,A2,B1}) |-> !$isunknown(Y))
    else $error("A21OI Y is X/Z with known inputs (A1=%b A2=%b B1=%b Y=%b)", A1, A2, B1, Y);

  // Full input space coverage (8 combos)
  cover property (!$isunknown({A1,A2,B1}) && {A1,A2,B1} == 3'b000);
  cover property (!$isunknown({A1,A2,B1}) && {A1,A2,B1} == 3'b001);
  cover property (!$isunknown({A1,A2,B1}) && {A1,A2,B1} == 3'b010);
  cover property (!$isunknown({A1,A2,B1}) && {A1,A2,B1} == 3'b011);
  cover property (!$isunknown({A1,A2,B1}) && {A1,A2,B1} == 3'b100);
  cover property (!$isunknown({A1,A2,B1}) && {A1,A2,B1} == 3'b101);
  cover property (!$isunknown({A1,A2,B1}) && {A1,A2,B1} == 3'b110);
  cover property (!$isunknown({A1,A2,B1}) && {A1,A2,B1} == 3'b111);

  // Output activity coverage
  cover property (Y == 1'b0);
  cover property (Y == 1'b1);
  cover property ($rose(Y));
  cover property ($fell(Y));

endmodule

// Bind into the DUT
bind sky130_fd_sc_hd__a21oi sky130_fd_sc_hd__a21oi_sva a21oi_sva_i (
  .A1(A1), .A2(A2), .B1(B1), .Y(Y)
);