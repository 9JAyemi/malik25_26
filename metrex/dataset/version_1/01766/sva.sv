// SVA for delay_one_cycle: 1-cycle pipeline with clean, glitch-free behavior
// Bind into the DUT so no RTL edits are required.

module delay_one_cycle_sva (
  input logic clk,
  input logic data,
  input logic to_pad,
  input logic delayed_data
);

  default clocking cb @(posedge clk); endclocking

  // Core behavior: to_pad is exactly data delayed by 1 clk
  property one_cycle_delay;
    !$isunknown($past(data)) |-> (to_pad == $past(data));
  endproperty
  assert property (one_cycle_delay);

  // If input holds its value, output holds its value
  assert property ( !$isunknown($past(data)) && (data == $past(data)) |-> (to_pad == $past(to_pad)) );

  // No spurious output changes: any change on to_pad must be due to a data change one cycle earlier
  assert property ( !$isunknown($past(data)) && $changed(to_pad) |-> $past($changed(data)) );

  // Edge-specific implications (redundant with core check but more diagnostic)
  assert property ( $rose(data) |=> to_pad );
  assert property ( $fell(data) |=> !to_pad );

  // Connectivity: output matches the registered stage
  assert property ( to_pad == delayed_data );

  // Basic functional coverage
  cover property ( $rose(data) ##1 to_pad );
  cover property ( $fell(data) ##1 !to_pad );
  cover property ( data != $past(data) ##1 (to_pad == $past(data)) );

endmodule

// Bind to DUT (connect internal reg for connectivity check)
bind delay_one_cycle delay_one_cycle_sva i_delay_one_cycle_sva (
  .clk(clk),
  .data(data),
  .to_pad(to_pad),
  .delayed_data(delayed_data)
);