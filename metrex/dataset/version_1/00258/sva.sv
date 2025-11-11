// SVA checker for d_ff_async_set_reset
module d_ff_async_set_reset_sva(
  input logic clk,
  input logic rst,
  input logic set,
  input logic d,
  input logic q,
  input logic q_bar
);
  default clocking cb @(posedge clk); endclocking
  default disable iff ($isunknown({rst,set,d,q,q_bar}));

  // Fundamental correctness: complementary outputs at all times
  ap_complement: assert property (q_bar == ~q)
    else $error("q_bar must be complement of q");

  // Reset dominates: regardless of set/d
  ap_rst:  assert property (rst |-> (q == 1'b0 && q_bar == 1'b1))
    else $error("Reset behavior violated");

  // Set when not reset
  ap_set:  assert property (!rst && set |-> (q == 1'b1 && q_bar == 1'b0))
    else $error("Set behavior violated");

  // Data capture when neither rst nor set
  ap_data: assert property (!rst && !set |-> (q == d && q_bar == ~q))
    else $error("Data capture/complement violated");

  // Explicit priority check when both asserted
  ap_both: assert property (rst && set |-> (q == 1'b0 && q_bar == 1'b1))
    else $error("Priority (rst over set) violated");

  // Optional sanity: outputs never equal (redundant with complement but clearer failure)
  ap_not_equal: assert property (q ^ q_bar)
    else $error("q and q_bar must differ");

  // Coverage: exercise all modes and transitions
  cp_rst:     cover property (rst);
  cp_set:     cover property (!rst && set);
  cp_both:    cover property (rst && set);
  cp_d0:      cover property (!rst && !set && d == 1'b0);
  cp_d1:      cover property (!rst && !set && d == 1'b1);
  cp_q_rise:  cover property (!rst && !set && $rose(q));
  cp_q_fall:  cover property (!rst && !set && $fell(q));
  cp_modes:   cover property (rst ##1 (!rst && set) ##1 (!rst && !set) ##1 (rst && set));
endmodule

// Bind into the DUT
bind d_ff_async_set_reset d_ff_async_set_reset_sva
  sva_i(.clk(clk), .rst(rst), .set(set), .d(d), .q(q), .q_bar(q_bar));