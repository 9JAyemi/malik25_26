// SVA for gtwizard_ultrascale_v1_7_1_bit_synchronizer
// Bind into DUT; uses internal regs and parameters directly.

module gtwizard_ultrascale_v1_7_1_bit_synchronizer_sva;

  // Default clocking
  default clocking cb @(posedge clk_in); endclocking

  // Track cycles since start to safely use $past
  int unsigned cycles;
  initial cycles = 0;
  always @(posedge clk_in) cycles++;

  // Power-up initialization checks (time 0)
  initial begin
    assert (i_in_meta  === INITIALIZE[0]) else $error("i_in_meta init != INITIALIZE[0]");
    assert (i_in_sync1 === INITIALIZE[1]) else $error("i_in_sync1 init != INITIALIZE[1]");
    assert (i_in_sync2 === INITIALIZE[2]) else $error("i_in_sync2 init != INITIALIZE[2]");
    assert (i_in_sync3 === INITIALIZE[3]) else $error("i_in_sync3 init != INITIALIZE[3]");
    assert (i_in_out   === INITIALIZE[4]) else $error("i_in_out init != INITIALIZE[4]");
    assert (o_out === i_in_out) else $error("o_out not tied to i_in_out at t0");
  end

  // Output wire must always mirror final flop
  assert property (o_out === i_in_out);

  // Stage-to-stage one-cycle transfer (guard unknowns; skip first cycle)
  assert property (disable iff (cycles == 0)
                   (!$isunknown($past(i_in)))        |-> i_in_meta  == $past(i_in));
  assert property (disable iff (cycles == 0)
                   (!$isunknown($past(i_in_meta)))    |-> i_in_sync1 == $past(i_in_meta));
  assert property (disable iff (cycles == 0)
                   (!$isunknown($past(i_in_sync1)))   |-> i_in_sync2 == $past(i_in_sync1));
  assert property (disable iff (cycles == 0)
                   (!$isunknown($past(i_in_sync2)))   |-> i_in_sync3 == $past(i_in_sync2));
  assert property (disable iff (cycles == 0)
                   (!$isunknown($past(i_in_sync3)))   |-> i_in_out   == $past(i_in_sync3));

  // End-to-end latency: o_out equals i_in delayed by 5 cycles (when known)
  assert property (disable iff (cycles < 5)
                   (!$isunknown($past(i_in,5))) |-> o_out == $past(i_in,5));

  // No fast path: after an i_in change, o_out must not change for the next 4 cycles
  assert property (disable iff (cycles < 5)
                   $changed(i_in) |-> ##1 (!$changed(o_out))[*4]);

  // Functional coverage: both polarities propagate with 5-cycle latency
  cover property (disable iff (cycles < 6) (i_in==0 ##1 i_in==1) ##5 (o_out==1));
  cover property (disable iff (cycles < 6) (i_in==1 ##1 i_in==0) ##5 (o_out==0));
  cover property (o_out==0);
  cover property (o_out==1);

endmodule

bind gtwizard_ultrascale_v1_7_1_bit_synchronizer gtwizard_ultrascale_v1_7_1_bit_synchronizer_sva;