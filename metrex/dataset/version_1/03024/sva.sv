// SVA for DFF and TLATCH
// Focused, high-quality checks + concise coverage

// DFF assertions
module DFF_sva(input logic D, CLK, EN, Q);
  // Avoid $past at first edge
  logic past_valid; initial past_valid = 0;
  always @(posedge CLK) past_valid <= 1;

  default clocking cb @(posedge CLK); endclocking

  // Functional correctness
  // On rising CLK with EN=1, Q must equal D
  assert property (cb EN |-> (Q == D));
  // On rising CLK with EN=0, Q must hold its previous value
  assert property (cb disable iff (!past_valid) !EN |-> (Q == $past(Q)));

  // No glitches: Q only changes on CLK rising edge
  assert property (@(posedge Q or negedge Q) $rose(CLK));

  // Sanity: no X/Z on key signals at sampling
  assert property (cb !$isunknown({D,EN,Q}));

  // Coverage
  cover property (cb EN && (Q == D));             // capture event
  cover property (cb disable iff (!past_valid) EN && (Q != $past(Q))); // Q toggled on capture
  cover property (cb disable iff (!past_valid) !EN && (Q == $past(Q))); // hold event
  cover property (cb disable iff (!past_valid) EN && ($past(Q)==0 && Q==1));
  cover property (cb disable iff (!past_valid) EN && ($past(Q)==1 && Q==0));
endmodule

bind DFF DFF_sva DFF_sva_i(.D(D), .CLK(CLK), .EN(EN), .Q(Q));


// TLATCH assertions (as-coded: posedge E sample + async clear on TE)
module TLATCH_sva(input logic D, E, TE, Q);
  // Async clear must force Q=0
  assert property (@(posedge TE) (Q == 1'b0));

  // On posedge E with TE=0, Q must capture D
  assert property (@(posedge E) (!TE |-> (Q == D)));

  // On posedge E with TE=1, Q must be 0 (clear dominates)
  assert property (@(posedge E) (TE |-> (Q == 1'b0)));

  // Q only changes on posedge E or posedge TE (no other glitches)
  assert property (@(posedge Q or negedge Q) ($rose(E) || $rose(TE)));

  // Forbid simultaneous posedges of E and TE (ambiguous behavior if both rise together)
  assert property (@(posedge E or posedge TE) !($rose(E) && $rose(TE)));

  // Sanity: no X/Z on key signals at relevant edges
  assert property (@(posedge E or posedge TE) !$isunknown({D,E,TE,Q}));

  // Coverage
  cover property (@(posedge TE) (Q == 1'b0));                 // async clear observed
  cover property (@(posedge E) (!TE && $changed(Q)));         // capture caused change
  cover property (@(posedge E) (TE && (Q == 1'b0)));          // E with TE high
endmodule

bind TLATCH TLATCH_sva TLATCH_sva_i(.D(D), .E(E), .TE(TE), .Q(Q));