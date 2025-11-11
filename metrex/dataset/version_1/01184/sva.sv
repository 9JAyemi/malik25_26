// SVA for Control_Register_Block
// Bind module (non-synth) with concise functional checks, X-checks, insensitivity, and coverage.

module Control_Register_Block_sva #(
  parameter int n = 4,
  parameter int m = 2,
  parameter logic [n-1:0] en1_ctrls = 4'b0001,
  parameter logic [n-1:0] en2_ctrls = 4'b0011
)(
  input logic [n-1:0] ctrl,
  input logic [m-1:0] en
);

  // Static sanity
  initial begin
    assert (m >= 2) else $error("Control_Register_Block: m must be >= 2");
    assert (n >= 1) else $error("Control_Register_Block: n must be >= 1");
  end

  default clocking cb @(ctrl); endclocking

  // Functional equivalence (exactly match DUT equations, 4-state aware)
  ap_en0_func: assert property (en[0] === ((ctrl & en1_ctrls) == en1_ctrls))
    else $error("en[0] != ((ctrl & en1_ctrls) == en1_ctrls)");
  ap_en1_func: assert property (en[1] === ((ctrl & en2_ctrls) == en2_ctrls))
    else $error("en[1] != ((ctrl & en2_ctrls) == en2_ctrls)");

  // X-propagation: when all required ctrl bits are known, output must be known
  ap_en0_known: assert property (!$isunknown(ctrl & en1_ctrls) |-> !$isunknown(en[0]))
    else $error("en[0] unknown while required ctrl bits are known");
  ap_en1_known: assert property (!$isunknown(ctrl & en2_ctrls) |-> !$isunknown(en[1]))
    else $error("en[1] unknown while required ctrl bits are known");

  // Insensitivity: bits outside mask must not affect enable (while masked bits stable)
  ap_en0_mask_insens: assert property ($stable(ctrl & en1_ctrls) && $changed(ctrl & ~en1_ctrls) |-> $stable(en[0]))
    else $error("en[0] changed due to non-masked ctrl bits");
  ap_en1_mask_insens: assert property ($stable(ctrl & en2_ctrls) && $changed(ctrl & ~en2_ctrls) |-> $stable(en[1]))
    else $error("en[1] changed due to non-masked ctrl bits");

  // Mask relationship: if en2 mask is a superset of en1 mask, then en[1] implies en[0]
  if ( (en2_ctrls & en1_ctrls) == en1_ctrls ) begin
    ap_hier_imply: assert property (en[1] |-> en[0])
      else $error("en[1] asserted without en[0] though en2_ctrls includes en1_ctrls");
  end

  // Coverage: basic states and toggles
  cv_en0_hi:   cover property (en[0]);
  cv_en1_hi:   cover property (en[1]);
  cv_en_both:  cover property (en[0] && en[1]);
  cv_en0_only: cover property (en[0] && !en[1]); // should be hit when ctrl == en1_ctrls and missing en2 extra bits
  cv_en_none:  cover property (!en[0] && !en[1]);

  cv_en0_rise: cover property ($rose(en[0]));
  cv_en0_fall: cover property ($fell(en[0]));
  cv_en1_rise: cover property ($rose(en[1]));
  cv_en1_fall: cover property ($fell(en[1]));

endmodule

// Bind into DUT (parameters inherit from instance)
bind Control_Register_Block Control_Register_Block_sva #(
  .n(n),
  .m(m),
  .en1_ctrls(en1_ctrls),
  .en2_ctrls(en2_ctrls)
) u_crb_sva (
  .ctrl(ctrl),
  .en(en)
);