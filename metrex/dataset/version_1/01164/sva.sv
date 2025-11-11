// SVA for DFF_SR_GATED
module DFF_SR_GATED_sva (input logic D,S,R,G,Q,QN);

  // Sample after NBA at posedge G so Q reflects the updated value
  clocking cb @(posedge G);
    default input #1step output #1step;
    input D,S,R,Q,QN;
  endclocking

  // Functional correctness (priority: R > S > D)
  assert property (@(cb) disable iff ($isunknown({cb.R,cb.S}))
                   cb.R |-> (cb.Q == 1'b0));

  assert property (@(cb) disable iff ($isunknown({cb.R,cb.S}))
                   (!cb.R && cb.S) |-> (cb.Q == 1'b1));

  assert property (@(cb) disable iff ($isunknown({cb.R,cb.S,cb.D}))
                   (!cb.R && !cb.S) |-> (cb.Q == cb.D));

  // Outputs known when inputs are known at the sampling edge
  assert property (@(cb) disable iff ($isunknown({cb.R,cb.S,cb.D}))
                   !$isunknown({cb.Q,cb.QN}));

  // QN is always the logical inverse of Q (checked on any change)
  assert property (@(posedge Q or negedge Q or posedge QN or negedge QN)
                   (!$isunknown({Q,QN})) |-> (QN == ~Q));

  // Coverage
  cover property (@(cb) cb.R && (cb.Q==0));                          // reset path
  cover property (@(cb) (!cb.R && cb.S) && (cb.Q==1));               // set path
  cover property (@(cb) (!cb.R && !cb.S && cb.D==0 && cb.Q==0));     // data=0 captured
  cover property (@(cb) (!cb.R && !cb.S && cb.D==1 && cb.Q==1));     // data=1 captured
  cover property (@(cb) (cb.R && cb.S) && (cb.Q==0));                // R&S both high, R wins
  cover property (@(cb) $past(cb.Q,1)===1'b0 && cb.Q===1'b1);        // 0->1 transition
  cover property (@(cb) $past(cb.Q,1)===1'b1 && cb.Q===1'b0);        // 1->0 transition

endmodule

bind DFF_SR_GATED DFF_SR_GATED_sva u_DFF_SR_GATED_sva (.*);