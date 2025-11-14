// SVA checker for glitch_filter
module glitch_filter_sva #(parameter int GD = 4) ();
  // Bound names: signal_in, signal_out, delay_line, filtered_signal, glitch_duration

  // Sanity on parameter
  initial assert (GD >= 2) else $error("glitch_duration must be >= 2");

  // Enable $past after first active edge
  bit have_past;
  initial have_past = 0;
  always @(posedge signal_in) have_past <= 1'b1;

  // Delay line shifts in current input at each posedge
  property p_shift;
    @(posedge signal_in) disable iff (!have_past)
      1'b1 |=> (delay_line == { $past(delay_line[GD-2:0]), $past(signal_in) });
  endproperty
  assert property (p_shift);

  // Filtered_signal update rule matches RTL branch
  property p_filtered;
    @(posedge signal_in) disable iff (!have_past)
      1'b1 |=> (filtered_signal ==
                ( ($past(delay_line[0]) && !$past(delay_line[GD-1]))
                  ? $past(delay_line[GD-2]) : $past(signal_in) ));
  endproperty
  assert property (p_filtered);

  // Output mirrors filtered_signal
  assert property (@(posedge signal_in or negedge signal_in) signal_out == filtered_signal);

  // Basic X check on output at activity
  assert property (@(posedge signal_in or negedge signal_in) !$isunknown(signal_out));

  // Coverage: both branches exercised and observable at output
  cover property (@(posedge signal_in) disable iff (!have_past)
                    ($past(delay_line[0]) && !$past(delay_line[GD-1]))
                    ##1 (signal_out == $past(delay_line[GD-2])));
  cover property (@(posedge signal_in) disable iff (!have_past)
                    (!($past(delay_line[0]) && !$past(delay_line[GD-1])))
                    ##1 (signal_out == $past(signal_in)));
endmodule

// Bind into DUT
bind glitch_filter glitch_filter_sva #(.GD(glitch_duration)) glitch_filter_sva_i();