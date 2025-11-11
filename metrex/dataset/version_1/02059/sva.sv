// SVA for servo_control
// Bindable, concise, and focused on key functional checks and coverage.

module servo_control_sva #(
  parameter int min_pulse_width = 1000,
  parameter int max_pulse_width = 2000,
  parameter int frequency       = 50,
  parameter int resolution      = 16
)(
  input logic        clk,
  input logic        rst,
  input logic [15:0] pwm_in,
  input logic [15:0] pwm_out,
  input logic [15:0] counter,
  input logic [15:0] threshold
);

  // Static/structural sanity
  initial begin
    assert (resolution > 0) else $error("resolution must be > 0");
    assert (min_pulse_width < max_pulse_width) else $error("min_pulse_width < max_pulse_width required");
  end

  // Clocking / reset control for sequential assertions
  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Reset behavior (not disabled on rst)
  assert property (@(posedge clk) rst |-> (counter==16'd0 && threshold==16'd0 && pwm_out==min_pulse_width))
    else $error("Reset values incorrect");
  assert property (@(posedge clk) rst && $past(rst) |-> (counter==16'd0 && threshold==16'd0 && pwm_out==min_pulse_width))
    else $error("State must hold during rst");

  // Counter behavior
  assert property ($past(counter) != resolution |-> counter == $past(counter)+16'd1)
    else $error("Counter must increment by 1 when not wrapping");
  assert property ($past(counter) == resolution |-> counter == 16'd0)
    else $error("Counter must wrap to 0 at resolution");
  assert property (counter <= resolution)
    else $error("Counter must never exceed resolution");

  // Threshold update/hold behavior
  assert property ($past(counter) == resolution |-> threshold == $past(pwm_in))
    else $error("Threshold must sample pwm_in on wrap");
  assert property ($past(counter) != resolution |-> threshold == $past(threshold))
    else $error("Threshold must hold when not wrapping");

  // Output correctness (combinational function based on previous cycle threshold/counter)
  assert property (pwm_out == ( ($past(threshold) > $past(counter)) ? max_pulse_width : min_pulse_width ))
    else $error("pwm_out must follow comparator decision from previous cycle");
  assert property (pwm_out == min_pulse_width || pwm_out == max_pulse_width)
    else $error("pwm_out must be either min or max only");

  // No X/Z on key state and outputs in operational mode
  assert property (!$isunknown({counter, threshold, pwm_out}))
    else $error("Unknown (X/Z) detected on state or outputs");

  // Coverage: wrap, both output states, and threshold update events
  cover property ($past(counter) == resolution && counter == 16'd0);                    // wrap event
  cover property (pwm_out == max_pulse_width);                                          // high output observed
  cover property (pwm_out == min_pulse_width);                                          // low output observed
  cover property ($past(counter) == resolution && threshold == $past(pwm_in));          // threshold update
  cover property ( ($past(threshold) > $past(counter)) && pwm_out == max_pulse_width ); // comparator true path
  cover property (!( $past(threshold) > $past(counter)) && pwm_out == min_pulse_width); // comparator false path

endmodule

// Bind into DUT
bind servo_control servo_control_sva #(
  .min_pulse_width(min_pulse_width),
  .max_pulse_width(max_pulse_width),
  .frequency      (frequency),
  .resolution     (resolution)
) servo_control_sva_i (
  .clk      (clk),
  .rst      (rst),
  .pwm_in   (pwm_in),
  .pwm_out  (pwm_out),
  .counter  (counter),
  .threshold(threshold)
);