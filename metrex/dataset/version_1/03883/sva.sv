// SVA for bmod/cmod: concise, high-quality checks and coverage

// Bind into cmod: functional correctness, X-propagation, stability, key coverage
module cmod_sva (input clk, input [31:0] n, input [31:0] result);
  default clocking cb @(posedge clk); endclocking

  // Functional relation must always hold
  ap_func:    assert property (result == n + 32'd1);

  // If input is known, output must be known (no X/Z propagation)
  ap_known:   assert property (!$isunknown(n) |-> !$isunknown(result));

  // If input holds its value, output must hold as well
  ap_stable:  assert property ($stable(n) |-> $stable(result));

  // Coverage: key corner/interesting points
  cp_zero:    cover property (n == 32'h0000_0000 && result == 32'h0000_0001);
  cp_mid:     cover property (n == 32'h1234_5678 && result == 32'h1234_5679);
  cp_wrap:    cover property (n == 32'hFFFF_FFFF && result == 32'h0000_0000);
  cp_hold:    cover property ($stable(n) && $stable(result));
endmodule

// Bind into bmod as a thin wrapper check to catch wiring issues
module bmod_sva (input clk, input [31:0] n, input [31:0] result);
  default clocking cb @(posedge clk); endclocking

  ap_func_wrap:  assert property (result == n + 32'd1);
  ap_known_wrap: assert property (!$isunknown(n) |-> !$isunknown(result));

  cp_wrap_wrap:  cover property (n == 32'hFFFF_FFFF && result == 32'h0000_0000);
endmodule

// Binds
bind cmod cmod_sva cmod_sva_i (.*);
bind bmod bmod_sva bmod_sva_i (.*);