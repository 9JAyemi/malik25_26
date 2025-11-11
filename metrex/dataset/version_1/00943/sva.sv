// SVA for address_operation
// Focus: correctness of q_a/q_b updates, no-X behavior, no glitches between clocks, and branch/overflow coverage.

module address_operation_sva (
  input  logic        clock,
  input  logic [8:0]  address_a,
  input  logic [8:0]  address_b,
  input  logic [3:0]  q_a,
  input  logic [3:0]  q_b
);

  default clocking cb @(posedge clock); endclocking

  // Expected results (4-bit wrap-around)
  let exp_a = (address_a[3:0] + (address_a[8] ? 4'd1 : 4'd2));
  let exp_b = (address_b[3:0] + (address_b[8] ? 4'd1 : 4'd2));

  // Functional correctness (sample outputs after RTL updates using ##0)
  ap_func_a: assert property (!$isunknown(address_a) |-> ##0 (q_a === exp_a) && !$isunknown(q_a))
    else $error("q_a mismatch: q_a=%0h addr_a=%0h exp=%0h", q_a, address_a, exp_a);

  ap_func_b: assert property (!$isunknown(address_b) |-> ##0 (q_b === exp_b) && !$isunknown(q_b))
    else $error("q_b mismatch: q_b=%0h addr_b=%0h exp=%0h", q_b, address_b, exp_b);

  // No glitches between clock edges (q_* can only change on posedge clock)
  ap_stable_between_edges_a: assert property (@(negedge clock) $stable(q_a))
    else $error("q_a changed between clock edges");
  ap_stable_between_edges_b: assert property (@(negedge clock) $stable(q_b))
    else $error("q_b changed between clock edges");

  // Simple input X-checks (flag X/Z on inputs at sampling edge)
  ap_no_x_inputs_a: assert property (!$isunknown(address_a))
    else $error("address_a has X/Z at posedge");
  ap_no_x_inputs_b: assert property (!$isunknown(address_b))
    else $error("address_b has X/Z at posedge");

  // Coverage: both branches taken for each port
  cover_a_msb1: cover property (address_a[8] == 1);
  cover_a_msb0: cover property (address_a[8] == 0);
  cover_b_msb1: cover property (address_b[8] == 1);
  cover_b_msb0: cover property (address_b[8] == 0);

  // Coverage: wrap-around edge cases
  cover_a_overflow_plus1: cover property (address_a[8] && address_a[3:0] == 4'hF ##0 q_a == 4'h0);
  cover_a_overflow_plus2_fF: cover property (!address_a[8] && address_a[3:0] == 4'hF ##0 q_a == 4'h1);
  cover_a_overflow_plus2_e:  cover property (!address_a[8] && address_a[3:0] == 4'hE ##0 q_a == 4'h0);

  cover_b_overflow_plus1: cover property (address_b[8] && address_b[3:0] == 4'hF ##0 q_b == 4'h0);
  cover_b_overflow_plus2_fF: cover property (!address_b[8] && address_b[3:0] == 4'hF ##0 q_b == 4'h1);
  cover_b_overflow_plus2_e:  cover property (!address_b[8] && address_b[3:0] == 4'hE ##0 q_b == 4'h0);

  // Coverage: outputs change at least once (exercise dynamic behavior)
  cover_a_changes: cover property (!$isunknown($past(q_a)) && q_a != $past(q_a));
  cover_b_changes: cover property (!$isunknown($past(q_b)) && q_b != $past(q_b));

endmodule

// Bind into DUT
bind address_operation address_operation_sva sva_i (
  .clock     (clock),
  .address_a (address_a),
  .address_b (address_b),
  .q_a       (q_a),
  .q_b       (q_b)
);