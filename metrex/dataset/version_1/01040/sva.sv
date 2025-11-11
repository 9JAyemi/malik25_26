// SVA checker for DLL. Bind this to the DUT to access internals.
module dll_sva #(
  parameter int delay = 5
)(
  input  logic        ref_clk,
  input  logic        data_in,
  input  logic        data_out,
  input  logic        delayed_ref_clk,
  input  logic [1:0]  phase_difference,
  input  logic [1:0]  loop_filter_output,
  input  logic [1:0]  loop_filter_state
);

  default clocking cb @(posedge ref_clk); endclocking

  // Start gating to avoid $past at time 0
  logic started;
  initial started = 1'b0;
  always @(posedge ref_clk) started <= 1'b1;

  // Environment sanity
  assume property (cb started |-> !$isunknown(data_in));

  // No X/Z propagation on internal state/outputs
  assert property (cb started |-> !$isunknown({delayed_ref_clk,phase_difference,loop_filter_output,loop_filter_state,data_out}));

  // phase_difference update: {pd1,pd0} = {pd0,data_in} ^ {drc,drc}
  assert property (cb disable iff (!started)
    ##0 phase_difference == { $past(phase_difference[0]) ^ $past(delayed_ref_clk),
                              $past(data_in)            ^ $past(delayed_ref_clk) });

  // loop_filter_output = prev_state + prev_phase_difference (mod 4)
  assert property (cb disable iff (!started)
    ##0 loop_filter_output == ($past(loop_filter_state) + $past(phase_difference)));

  // loop_filter_state registers loop_filter_output
  assert property (cb disable iff (!started)
    ##0 loop_filter_state == $past(loop_filter_output));

  // Equivalent accumulator check (redundant but strong): state(n+1) = state(n) + pd(n)
  assert property (cb disable iff (!started)
    ##0 loop_filter_state == ($past(loop_filter_state) + $past(phase_difference)));

  // data_out holds previous cycle's data_in at each posedge (pre-NBA sampling)
  assert property (cb disable iff (!started)
    data_out == $past(data_in));

  // If delayed_ref_clk==0, data_out updates immediately in same timestep (post-NBA)
  assert property (cb disable iff (!started)
    !delayed_ref_clk |-> ##0 (data_out == data_in));

  // Basic functional coverage
  cover property (cb started ##0 (phase_difference == 2'b00));
  cover property (cb started ##0 (phase_difference == 2'b01));
  cover property (cb started ##0 (phase_difference == 2'b10));
  cover property (cb started ##0 (phase_difference == 2'b11));

  // Exercise both data_out update paths
  cover property (cb started && !delayed_ref_clk ##0 (data_out == data_in));        // immediate path
  cover property (cb started &&  delayed_ref_clk ##1 (data_out == $past(data_in))); // deferred path observed next posedge

  // Show loop_filter wrap-around (carry)
  cover property (cb started && (loop_filter_state == 2'b11) ##1 (loop_filter_state == 2'b00));

endmodule

// Bind checker into the DUT, exposing internals
bind DLL dll_sva #(.delay(delay)) dll_sva_i (
  .ref_clk(ref_clk),
  .data_in(data_in),
  .data_out(data_out),
  .delayed_ref_clk(delayed_ref_clk),
  .phase_difference(phase_difference),
  .loop_filter_output(loop_filter_output),
  .loop_filter_state(loop_filter_state)
);