// SVA for pulse_detection
module pulse_detection_sva #(
  parameter int unsigned CNT_HIT = 32'd100000000,
  parameter int unsigned DIV     = 32'd100000
)(
  input logic               clk,
  input logic               reset,
  // DUT I/Os and internals (bind by name)
  input logic [31:0]        in,
  input logic [15:0]        threshold,
  input logic [15:0]        frequency,
  input logic               threshold_exceeded,
  input logic [31:0]        count,
  input logic [3:0]         prescaler,
  input logic [31:0]        prev_in,
  input logic [31:0]        curr_in
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset)

  // Shorthands
  let sample = (prescaler == 4'd0);                // sampling cycle
  let rise   = (prev_in == 32'd0 && curr_in == 32'd1); // rising detect per RTL

  // Async reset clears (checked during reset)
  assert property (@(posedge clk) reset |-> (count==0 && prescaler==0 && prev_in==0 && curr_in==0 && frequency==0 && threshold_exceeded==0));

  // Prescaler range and behavior
  assert property (prescaler inside {[4'd0:4'd15]});
  assert property ( sample  |=> prescaler == 4'd15);
  assert property (!sample  |=> prescaler == $past(prescaler) - 4'd1);
  assert property ( sample  |-> !sample[*15] ##1 sample); // exactly 16-cycle period between samples

  // Sampling of inputs
  assert property ( sample  |=> (prev_in == $past(curr_in) && curr_in == $past(in)));
  assert property (!sample  |=> (prev_in == $past(prev_in) && curr_in == $past(curr_in)));

  // Count progression (no threshold event this cycle)
  assert property ( (count < CNT_HIT && sample && rise)         |=> count == $past(count) + 32'd1 );
  assert property ( (count < CNT_HIT && !(sample && rise))      |=> count == $past(count)        );

  // Threshold event: uses pre-state count per RTL, resets count and updates frequency
  assert property ( (count >= CNT_HIT) |=> (count == 0) );
  assert property ( (count >= CNT_HIT) |=> (frequency == ($past(count) / DIV)) );
  // threshold_exceeded is driven from pre-update frequency per RTL
  assert property ( (count >= CNT_HIT) |=> (threshold_exceeded == ($past(frequency) > threshold)) );

  // No spurious updates when no threshold event
  assert property ( (count < CNT_HIT) |=> (frequency == $past(frequency)) );
  assert property ( (count < CNT_HIT) |=> (threshold_exceeded == $past(threshold_exceeded)) );

  // Any count change must be a valid increment or a threshold reset
  assert property (
    (count != $past(count)) |->
      ( ($past(count) < CNT_HIT && sample && rise && count == $past(count)+32'd1)
        || ($past(count) >= CNT_HIT && count == 32'd0) )
  );

  // Coverage
  cover property (sample && rise);                        // a detected pulse at a sample
  cover property (sample ##[15:15] sample);               // prescaler wrap period observed
  cover property ((count >= CNT_HIT));                    // threshold event occurs
  cover property ((count >= CNT_HIT) ##1 !threshold_exceeded); // threshold_exceeded=0 path
  cover property ((count >= CNT_HIT) ##1  threshold_exceeded); // threshold_exceeded=1 path

endmodule

bind pulse_detection pulse_detection_sva sva_inst (.*);