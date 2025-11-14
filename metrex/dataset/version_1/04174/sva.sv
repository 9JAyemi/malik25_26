// SVA checker for iscachable
// Bind this module to iscachable and connect a sampling clock from your env.
module iscachable_sva (
  input logic               clk,
  input logic [29:0]        i_addr,
  input logic               o_cachable
);
  default clocking cb @ (posedge clk); endclocking

  // Decode conditions (mirrors DUT)
  logic a_dec, b_dec, c_dec;
  assign a_dec = ((i_addr & 30'h3e000000) == 30'h1a000000);
  assign b_dec = ((i_addr & 30'h3e000000) == 30'h1c000000);
  assign c_dec = ((i_addr & 30'h20000000) == 30'h20000000);

  // Functional equivalence: o_cachable must be the OR of the three decodes
  ap_func_eq: assert property (o_cachable == (a_dec || b_dec || c_dec))
    else $error("iscachable: functional mismatch");

  // Known-ness: when addr is known, output must be known
  ap_known: assert property (!$isunknown(i_addr) |-> !$isunknown(o_cachable))
    else $error("iscachable: o_cachable X/Z while i_addr known");

  // Combinational stability: if addr is stable cycle-to-cycle, output must be stable
  ap_stable: assert property ($stable(i_addr) |-> $stable(o_cachable))
    else $error("iscachable: o_cachable changed without i_addr change");

  // Decode uniqueness: the two masked region decodes cannot overlap
  ap_unique: assert property (!(a_dec && b_dec))
    else $error("iscachable: overlapping a_dec and b_dec (should be impossible)");

  // Coverage: hit each cachable class and the non-cachable region
  cp_a:     cover property (a_dec && o_cachable);
  cp_b:     cover property (b_dec && o_cachable);
  cp_c:     cover property (c_dec && o_cachable);
  cp_none:  cover property (!(a_dec || b_dec || c_dec) && !o_cachable);

  // Optional: observe both output transitions at least once
  cp_rise:  cover property (!o_cachable ##1 o_cachable);
  cp_fall:  cover property ( o_cachable ##1 !o_cachable);

endmodule

// Example bind (hook clk from your environment)
// bind iscachable iscachable_sva u_iscachable_sva (.clk(clk), .i_addr(i_addr), .o_cachable(o_cachable));