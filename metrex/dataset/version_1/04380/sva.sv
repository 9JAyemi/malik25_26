// SVA for binary_adder
// Focus: reset behavior, registered next-state equations, carry logic, and key coverage.
// Bind-friendly: accesses internal regs sum/carry via ports.

package binary_adder_sva_pkg;
  function automatic logic maj3(logic a,b,c);
    return (a&b) | (a&c) | (b&c);
  endfunction
endpackage

module binary_adder_sva (
  input logic        clk,
  input logic        reset,      // async active-low in DUT, but used as active-high enable for checks
  input logic [3:0]  A,
  input logic [3:0]  B,
  input logic [3:0]  S,
  input logic [3:0]  carry,      // DUT internal
  input logic [3:0]  sum         // DUT internal
);
  import binary_adder_sva_pkg::*;

  default clocking cb @(posedge clk); endclocking
  default disable iff (!reset);

  // Structural tie-off
  ap_s_eq_sum: assert property (S == sum);

  // Hold zeros while in reset at each clock
  ap_hold_zero_in_reset: assert property (@(posedge clk) !reset |-> (carry==4'h0 && sum==4'h0 && S==4'h0));

  // Registered next-state equations (values at this edge equal function of last edge)
  ap_sum_update:  assert property (reset && $past(reset)
                                   |-> sum == (($past(A) + $past(B) + $past(carry)) & 4'hF));

  ap_carry_update: assert property (reset && $past(reset)
                                    |-> (carry[3:1] == $past(carry[2:0])) &&
                                        (carry[0]   == maj3($past(A[3]), $past(B[3]), $past(carry[3]))));

  // Known-state check when active
  ap_known_active: assert property (reset |-> !$isunknown({sum,carry,S}));

  // Minimal coverage
  cp_reset_seq:       cover property (@(posedge clk) !reset ##1 reset);
  cp_simple_add:      cover property (reset && $past(reset) && ($past(carry)==4'h0) &&
                                      (sum == (($past(A)+$past(B)) & 4'hF)));
  cp_overflow_wrap:   cover property (reset && $past(reset) &&
                                      (($past(A)+$past(B)+$past(carry)) >= 16) &&
                                      (sum == (($past(A)+$past(B)+$past(carry)) & 4'hF)));
  cp_maj0:            cover property (reset && $past(reset) &&
                                      (maj3($past(A[3]),$past(B[3]),$past(carry[3]))==1'b0));
  cp_maj1:            cover property (reset && $past(reset) &&
                                      (maj3($past(A[3]),$past(B[3]),$past(carry[3]))==1'b1));
endmodule

// Bind into the DUT
bind binary_adder binary_adder_sva u_binary_adder_sva (
  .clk   (clk),
  .reset (reset),
  .A     (A),
  .B     (B),
  .S     (S),
  .carry (carry),
  .sum   (sum)
);