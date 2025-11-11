// SVA for shift_register_counter
// Bind into DUT: bind shift_register_counter shift_register_counter_sva sva(.clk(clk), .reset(reset), .areset(areset), .load(load), .ena(ena), .data(data), .shift_out(shift_out), .counter_out(counter_out));

module shift_register_counter_sva (
  input  logic        clk,
  input  logic        reset,    // active-low async in RTL
  input  logic        areset,   // active-low async in RTL
  input  logic        load,
  input  logic        ena,
  input  logic [3:0]  data,
  input  logic [3:0]  shift_out,
  input  logic [3:0]  counter_out
);

  default clocking cb @(posedge clk); endclocking

  // -------------------------
  // Shift register assertions
  // -------------------------

  // Async areset immediately clears shift_out to 0 on negedge areset, and holds 0 while low
  assert property (@(negedge areset) 1 |-> ##0 (shift_out == 4'b0000));
  assert property ( !areset |-> (shift_out == 4'b0000) );

  // Load behavior (load has priority over ena); check on next cycle
  assert property ( areset && $past(areset) && load |=> shift_out == $past(data) );

  // Rotate-left by 1 when ena and no load; check on next cycle
  assert property ( areset && $past(areset) && !load && ena
                    |=> shift_out == { $past(shift_out[2:0]), $past(shift_out[3]) } );

  // Hold when neither load nor ena
  assert property ( areset && $past(areset) && !load && !ena
                    |=> shift_out == $past(shift_out) );

  // Explicitly check load priority over ena when both asserted
  assert property ( areset && $past(areset) && load && ena
                    |=> shift_out == $past(data) );

  // ---------------------
  // Counter assertions
  // ---------------------

  // Async reset immediately clears counter_out to 0 on negedge reset, and holds 0 while low
  assert property (@(negedge reset) 1 |-> ##0 (counter_out == 4'b0000));
  assert property ( !reset |-> (counter_out == 4'b0000) );

  // When out of reset (stable high), counter increments by 1 each cycle
  assert property ( reset && $past(reset) |=> counter_out == $past(counter_out) + 4'd1 );

  // Wrap from 0xF to 0x0 (implied by +1 modulo 16) when out of reset
  assert property ( reset && $past(reset) && ($past(counter_out) == 4'hF)
                    |=> counter_out == 4'h0 );

  // ---------------------
  // Sanity/consistency
  // ---------------------

  // No X on outputs when corresponding reset is high (stable) at consecutive cycles
  assert property ( areset && $past(areset) |-> !$isunknown(shift_out) );
  assert property ( reset  && $past(reset)  |-> !$isunknown(counter_out) );

  // ---------------------
  // Coverage
  // ---------------------

  // See load action
  cover property ( areset && $past(areset) && load );

  // See rotate action
  cover property ( areset && $past(areset) && !load && ena
                   && shift_out == { $past(shift_out[2:0]), $past(shift_out[3]) } );

  // See idle/hold
  cover property ( areset && $past(areset) && !load && !ena
                   && shift_out == $past(shift_out) );

  // See both load and ena (priority case)
  cover property ( areset && $past(areset) && load && ena
                   |=> shift_out == $past(data) );

  // Counter wrap coverage
  cover property ( reset && $past(reset) && ($past(counter_out) == 4'hF)
                   && (counter_out == 4'h0) );

  // Async reset pulses observed
  cover property (@(negedge areset) 1);
  cover property (@(negedge reset)  1);

endmodule

// Example bind (uncomment in your TB):
// bind shift_register_counter shift_register_counter_sva sva (.*);