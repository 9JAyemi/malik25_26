// SVA for top_module
// Bind this module to the DUT: bind top_module top_module_sva sva();

module top_module_sva;

  // Use DUT signals via bind scope
  // Clocking and reset
  default clocking cb @(negedge clk); endclocking
  default disable iff (reset);

  // Async reset puts regs to known values (sample after update using ##0)
  assert property (@(posedge reset) ##0 (shift_reg == 8'b00110100
                                      && johnson_counter == 4'b0000
                                      && sum == 12'b0000_0000_0000));

  // Shift register behavior
  // Load has highest priority
  assert property (load |=> shift_reg == $past(data_in));

  // Rotate left when shift_direction==2'b00 and not loading
  assert property ((!load && shift_direction == 2'b00)
                   |=> shift_reg == { $past(shift_reg[6:0]), $past(shift_reg[7]) });

  // Rotate right when shift_direction==2'b01 and not loading
  assert property ((!load && shift_direction == 2'b01)
                   |=> shift_reg == { $past(shift_reg[0]), $past(shift_reg[7:1]) });

  // Hold when shift_direction is other values and not loading
  assert property ((!load && !(shift_direction inside {2'b00,2'b01}))
                   |=> shift_reg == $past(shift_reg));

  // Johnson counter behavior
  assert property ( slowena |=> johnson_counter == $past(johnson_counter) + 4'd1 );
  assert property (!slowena |=> johnson_counter == $past(johnson_counter) );

  // Sum updates to concatenation of previous-cycle regs
  assert property ( sum == { $past(shift_reg), $past(johnson_counter) } );

  // Output tie-off
  assert property ( output_sum == sum );

  // -----------------
  // Functional coverage
  // -----------------
  // Reset observed
  cover property (@(posedge reset) 1);

  // Exercise load and both rotations and hold
  cover property (load);
  cover property (!load && shift_direction == 2'b00);
  cover property (!load && shift_direction == 2'b01);
  cover property (!load && !(shift_direction inside {2'b00,2'b01}));

  // Counter increment and wrap-around
  cover property ( slowena );
  cover property ( (johnson_counter == 4'hF && slowena) |=> (johnson_counter == 4'h0) );

endmodule

bind top_module top_module_sva sva();