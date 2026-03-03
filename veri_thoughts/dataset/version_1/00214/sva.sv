// SVA for sync_resettable_latch
// Concise, high-quality checks and coverage

module sync_resettable_latch_sva #(parameter WIDTH=4)
(
  input logic                 CLK,
  input logic                 EN,
  input logic                 RST,
  input logic [WIDTH-1:0]     D,
  input logic [WIDTH-1:0]     Q
);

  // Clocking and past-valid guard
  default clocking cb @(posedge CLK); endclocking
  logic past_valid;
  always_ff @(posedge CLK) past_valid <= 1'b1;
  default disable iff (!past_valid);

  // Sanity/cleanliness
  a_ctrl_known:       assert property (!$isunknown({EN,RST}));
  a_d_known_when_en:  assert property (EN |-> !$isunknown(D));
  a_q_known:          assert property (!$isunknown(Q));

  // Functional behavior
  a_load:      assert property (EN              |=> Q == $past(D));
  a_reset:     assert property (!EN && RST      |=> Q == '0);
  a_hold:      assert property (!EN && !RST     |=> $stable(Q));
  a_priority:  assert property (EN && RST       |=> Q == $past(D)); // EN wins over RST
  a_change_gated: assert property ($changed(Q)  |-> $past(EN || RST));

  // No glitches between clocks (spot-check at opposite edge)
  a_no_glitch: assert property (@(negedge CLK) $stable(Q));

  // Coverage (all key branches and priority)
  c_load_change:         cover property ( $past(EN && !RST) ##1 (Q == $past(D) && Q != $past(Q)) );
  c_reset_from_nonzero:  cover property ( ($past(!EN && RST) && ($past(Q) != '0)) ##1 (Q == '0) );
  c_hold:                cover property ( $past(!EN && !RST) ##1 (Q == $past(Q)) );
  c_both_high:           cover property ( $past(EN && RST)   ##1 (Q == $past(D)) );

endmodule

bind sync_resettable_latch sync_resettable_latch_sva #(.WIDTH(4))
  u_sva (.CLK(CLK), .EN(EN), .RST(RST), .D(D), .Q(Q));