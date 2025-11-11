// SVA checker bound to top_module. Focuses on functional correctness, reset behavior,
// handshake relations, and key coverage. Concise but high-value checks.

module top_sva (top_module dut);

  default clocking cb @(posedge dut.clk); endclocking

  // -----------------------
  // Combinational datapath
  // -----------------------

  // sum_module correctness (select is intentionally unused)
  assert property (dut.out == {dut.shift_out, dut.accum_out});

  // shift_left_module functional intent: pure left shift
  // (Will catch the RTL bug and illegal shift_amount=0 corner)
  assert property (dut.shift_out == (dut.in << dut.shift_amount));

  // select has no effect on out (detect dead input)
  assert property (
    $changed(dut.select) && $stable(dut.shift_out) && $stable(dut.accum_out)
    |-> $stable(dut.out)
  );

  // No X/Z on key outputs when out of reset
  assert property (dut.rst_n |-> !$isunknown({dut.out, dut.ready_a, dut.valid_b}));

  // -----------------------
  // Accumulator correctness
  // -----------------------

  // Async reset drives zero immediately at negedge rst_n
  assert property (@(negedge dut.rst_n) dut.accum_out == 8'h00);

  // While in reset, output held at zero
  assert property (!dut.rst_n |-> dut.accum_out == 8'h00);

  // On each rising clock when not in reset, accumulate with wrap-around
  assert property (dut.rst_n && $past(dut.rst_n)
                   |-> dut.accum_out == $past(dut.accum_out) + $past(dut.data_in));

  // -----------------------
  // Handshake relations
  // -----------------------

  // Output channel validity mirrors ready_b
  assert property (dut.valid_b == dut.ready_b);

  // Input ready relation
  assert property (dut.ready_a == (~dut.valid_a | dut.valid_b));

  // -----------------------
  // Coverage
  // -----------------------

  // Exercise shift extremes and typical values
  cover property (dut.rst_n && dut.shift_amount == 0);
  cover property (dut.rst_n && dut.shift_amount == 1);
  cover property (dut.rst_n && dut.shift_amount == 63);

  // Accumulator wrap-around coverage
  cover property (dut.rst_n && $past(dut.rst_n) &&
                  (dut.accum_out < $past(dut.accum_out)));

  // Handshake coverage: backpressure clears
  cover property (dut.valid_a && !dut.ready_a ##1 dut.ready_a);

  // Select toggles observed
  cover property (dut.rst_n && $changed(dut.select));

endmodule

bind top_module top_sva i_top_sva (.dut());