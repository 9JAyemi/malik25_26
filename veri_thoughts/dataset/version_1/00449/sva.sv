// SVA for DLATCHR
module DLATCHR_sva (
  input logic D,
  input logic nCLK,
  input logic nRST,
  input logic INIT,
  input logic Q
);

  default clocking cb @(posedge nCLK); endclocking

  // Functional correctness: Q equals the mux of prior-cycle inputs
  assert property ($past(1'b1) |-> (Q == $past(nRST ? D : INIT)));

  // Inputs known at sampling; Q known after first sampled cycle
  assert property (!$isunknown({nRST, D, INIT}));
  assert property ($past(1'b1) |-> !$isunknown(Q));

  // Q changes only on clock edges (no glitches)
  property q_changes_only_on_clk;
    @(posedge nCLK or posedge Q or negedge Q)
      $changed(Q) |-> $rose(nCLK);
  endproperty
  assert property (q_changes_only_on_clk);

  // Coverage: exercise reset load, data capture, and reset release then capture
  cover property (!nRST ##1 (Q == $past(INIT)));
  cover property ( nRST ##1 (Q == $past(D)));
  cover property (!nRST ##1 nRST ##1 (Q == $past(D)));

endmodule

bind DLATCHR DLATCHR_sva sva_i (.D(D), .nCLK(nCLK), .nRST(nRST), .INIT(INIT), .Q(Q));