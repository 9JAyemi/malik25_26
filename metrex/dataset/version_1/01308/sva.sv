// SVA for d_ff_en: q updates to d on posedge clk only when en && te; otherwise q holds.

module d_ff_en_sva(input logic clk, en, te, d, q);
  // Guard $past on first cycle
  logic past_valid;
  initial past_valid = 1'b0;
  always_ff @(posedge clk) past_valid <= 1'b1;

  default clocking cb @(posedge clk); endclocking
  default disable iff (!past_valid);

  // Functional correctness
  // When both enables are 1, q must take d on the next cycle
  assert property ( (en===1'b1 && te===1'b1) |=> (q === $past(d)) );

  // When not both 1 (including X/Z), q must hold its previous value
  assert property ( !(en===1'b1 && te===1'b1) |=> (q === $past(q)) );

  // Any change on q must be caused by a gated update in the prior cycle
  assert property ( (q != $past(q)) |-> $past(en===1'b1 && te===1'b1) );

  // Coverage
  cover property ( (en===1'b1 && te===1'b1 && d===1'b0) |=> (q===1'b0) );
  cover property ( (en===1'b1 && te===1'b1 && d===1'b1) |=> (q===1'b1) );
  cover property ( (en===1'b1 && te===1'b0) |=> (q===$past(q)) );
  cover property ( (en===1'b0 && te===1'b1) |=> (q===$past(q)) );
  cover property ( (en===1'b1 && te===1'b1)[*2] ); // back-to-back updates possible
endmodule

// Bind to DUT
bind d_ff_en d_ff_en_sva u_d_ff_en_sva(.clk(clk), .en(en), .te(te), .d(d), .q(q));