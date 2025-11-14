`ifndef SYNTHESIS
// SVA for sky130_fd_sc_lp__inputiso1p (X = A | SLEEP)
module sky130_fd_sc_lp__inputiso1p_sva (
  input logic A,
  input logic SLEEP,
  input logic X,
  input logic VPWR,
  input logic VGND,
  input logic VPB,
  input logic VNB
);

  // Sample on any relevant change
  event comb_ev = (A or SLEEP or X);

  // Functional correctness
  assert property (@comb_ev SLEEP |-> (X === 1'b1));
  assert property (@comb_ev (!SLEEP && !$isunknown(A)) |-> (X === A));
  assert property (@comb_ev (!$isunknown({A,SLEEP})) |-> !$isunknown(X));

  // Logical implications of OR
  assert property (@comb_ev (X === 1'b0) |-> (!SLEEP && !A));
  assert property (@comb_ev (X === 1'b1) |-> (SLEEP || A));

  // Change-response checks
  assert property (@comb_ev (!SLEEP && $changed(A) && !$isunknown(A)) |-> ($changed(X) && X === A));
  assert property (@comb_ev ( SLEEP && $changed(A)) |-> (!$changed(X) && X === 1'b1));
  assert property (@comb_ev $changed(SLEEP) |-> (X === (SLEEP ? 1'b1 : A)));

  // Coverage: all input combos and key transitions
  cover property (@comb_ev (!SLEEP && !A && X === 1'b0));
  cover property (@comb_ev (!SLEEP &&  A && X === 1'b1));
  cover property (@comb_ev ( SLEEP && !A && X === 1'b1));
  cover property (@comb_ev ( SLEEP &&  A && X === 1'b1));
  cover property (@comb_ev (!SLEEP && $changed(A) && X === A));
  cover property (@comb_ev ($rose(SLEEP) && X === 1'b1));
  cover property (@comb_ev ($fell(SLEEP) && !$isunknown(A) && X === A));

  // Power rails constant (as modeled)
  initial begin
    assert (VPWR === 1'b1);
    assert (VGND === 1'b0);
    assert (VPB  === 1'b1);
    assert (VNB  === 1'b0);
  end
endmodule

bind sky130_fd_sc_lp__inputiso1p sky130_fd_sc_lp__inputiso1p_sva sva_i (
  .A(A), .SLEEP(SLEEP), .X(X), .VPWR(VPWR), .VGND(VGND), .VPB(VPB), .VNB(VNB)
);
`endif