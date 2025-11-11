// SVA checker for Clock_Divider
module Clock_Divider_sva (
  input logic        clock,
  input logic        reset,
  input logic [1:0]  counter,
  input logic        clock_out
);

  default clocking cb @(posedge clock); endclocking

  // Async reset takes effect immediately
  assert property (@(posedge reset) ##0 (counter==2'b00 && clock_out==1'b0));

  // Held in reset
  assert property (reset |-> (counter==2'b00 && clock_out==1'b0));

  // Counter stays in 0,1,2
  assert property (disable iff (reset) counter inside {2'b00,2'b01,2'b10});

  // Normal increment when not wrapping; output stable
  assert property (disable iff (reset)
    ($past(!reset) && $past(counter)!=2'b10) |-> (counter==$past(counter)+2'b01 && clock_out==$past(clock_out)));

  // Wrap at 2 -> 0 and toggle output
  assert property (disable iff (reset)
    ($past(!reset) && $past(counter)==2'b10) |-> (counter==2'b00 && clock_out!=$past(clock_out)));

  // Output toggles only on wrap
  assert property (disable iff (reset)
    $changed(clock_out) |-> ($past(!reset) && $past(counter)==2'b10));

  // Output toggles every 3 clocks (no early toggles)
  assert property (disable iff (reset)
    $changed(clock_out) |=> !$changed(clock_out) ##1 !$changed(clock_out) ##1 $changed(clock_out));

  // Coverage
  cover property (disable iff (reset)
    counter==2'b00 ##1 counter==2'b01 ##1 counter==2'b10 ##1 (counter==2'b00 && $changed(clock_out)));

  cover property (disable iff (reset)
    $changed(clock_out) ##3 $changed(clock_out));

  cover property (disable iff (reset) clock_out==1'b1);
  cover property (@(posedge reset) 1'b1);

endmodule

// Bind into DUT
bind Clock_Divider Clock_Divider_sva u_clock_divider_sva (
  .clock(clock),
  .reset(reset),
  .counter(counter),
  .clock_out(clock_out)
);