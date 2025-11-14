// SVA for waveform_generator
module waveform_generator_sva #(parameter int W = 32) (
  input  logic       X,
  input  logic [W-1:0] waveform,
  input  int         time
);

  // Initial state checks
  initial begin
    assert (time == 0) else $error("time not initialized to 0");
    assert (waveform == '0) else $error("waveform not initialized to 0");
  end

  default clocking cb @(posedge X); endclocking

  // time increments by exactly 1 on each posedge X
  property inc_time_p;
    1'b1 |=> time == $past(time) + 1;
  endproperty
  assert property (inc_time_p);

  // Index used (previous time) must be within waveform bounds
  property index_in_range_p;
    1'b1 |=> $past(time) inside {[0:W-1]};
  endproperty
  assert property (index_in_range_p);

  // Exactly one bit changes per posedge (the targeted bit)
  property one_bit_changes_p;
    1'b1 |=> $onehot(waveform ^ $past(waveform));
  endproperty
  assert property (one_bit_changes_p);

  // The targeted bit is set to 1 (since X is 1 at posedge)
  property write_correct_bit_p;
    1'b1 |=> waveform[$past(time)] == 1'b1;
  endproperty
  assert property (write_correct_bit_p);

  // No bit ever clears
  property no_bit_clear_p;
    1'b1 |=> (($past(waveform) & ~waveform) == '0);
  endproperty
  assert property (no_bit_clear_p);

  // No updates occur on negedge X
  assert property (@(negedge X) $stable(time) && $stable(waveform));

  // Coverage
  cover property (@(posedge X) time == 1 && waveform[0]);                               // first write
  cover property (@(posedge X) $past(time) == W-1 |=> (time == W && waveform[W-1]));    // last in-range write
  cover property (@(posedge X) waveform == '1);                                         // all bits set
  cover property (@(posedge X) time > W-1);                                             // overflow/OOO index reached (bug exposure)

endmodule

// Bind into DUT
bind waveform_generator waveform_generator_sva #(.W(32)) wfg_sva_i (
  .X(X),
  .waveform(waveform),
  .time(time)
);