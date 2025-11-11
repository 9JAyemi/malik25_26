// SVA for top_module: concise, high-quality checks and coverage.
// Uses event-based clocking and ##0 to sample after NBA updates.

module top_module_sva (
  input  logic [15:0] data_in,
  input  logic [3:0]  LOAD,
  input  logic [3:0]  Q,
  input  logic [3:0]  ones_count,
  input  logic [3:0]  final_output
);

  // Known-value checks (guarded by inputs known)
  a_boc_known:   assert property (@(data_in) !$isunknown(data_in) |-> ##0 !$isunknown(ones_count));
  a_udc_known:   assert property (@(LOAD)   !$isunknown(LOAD)   |-> ##0 !$isunknown(Q));
  a_adder_known: assert property (@(ones_count or Q)
                                  (!$isunknown({ones_count,Q})) |-> ##0 !$isunknown(final_output));

  // Binary ones counter must equal popcount (mod 16)
  a_boc_functional: assert property (@(data_in) 1 |-> ##0 (ones_count == $countones(data_in)[3:0]));

  // Up-down "counter" (load-through) behavior: Q follows LOAD on change
  a_udc_update:      assert property (@(LOAD) 1 |-> ##0 (Q == LOAD));

  // Adder: SUM is truncated 4-bit sum of operands
  a_adder_functional: assert property (@(ones_count or Q) 1 |-> ##0 (final_output == (ones_count + Q)));

  // End-to-end check: final_output = popcount(data_in)[3:0] + LOAD (mod 16)
  a_top_end_to_end:   assert property (@(data_in or LOAD)
                                      1 |-> ##0 (final_output == ($countones(data_in)[3:0] + LOAD)));

  // Coverage
  c_boc_0:   cover property (@(data_in) $countones(data_in) == 0);
  c_boc_1:   cover property (@(data_in) $countones(data_in) == 1);
  c_boc_8:   cover property (@(data_in) $countones(data_in) == 8);
  c_boc_15:  cover property (@(data_in) $countones(data_in) == 15);
  c_boc_16:  cover property (@(data_in) $countones(data_in) == 16);

  c_udc_min: cover property (@(LOAD) LOAD == 4'd0  ##0 Q == 4'd0);
  c_udc_max: cover property (@(LOAD) LOAD == 4'd15 ##0 Q == 4'd15);

  c_add_ovf:    cover property (@(data_in or LOAD) ($countones(data_in) + LOAD) >= 16);
  c_add_no_ovf: cover property (@(data_in or LOAD) ($countones(data_in) + LOAD) < 16);

endmodule

bind top_module top_module_sva sva_i (.*);