// SVA for vending_machine
// Bind into DUT; checks state machine correctness, outputs, priorities, and dispense handshake.
// Includes focused functional coverage.
module vending_machine_sva (vending_machine dut);

  default clocking cb @(posedge dut.clk); endclocking
  default disable iff (dut.reset);

  localparam S_IDLE = 2'b00;
  localparam S_X    = 2'b01;
  localparam S_Y    = 2'b10;
  localparam S_Z    = 2'b11;

  // Sanity
  assert property (@cb !$isunknown({dut.current_state, dut.product_X_selected, dut.product_Y_selected, dut.product_Z_selected, dut.dispensed})))
    else $error("Unknown/X on state or outputs");
  assert property (@cb dut.current_state inside {S_IDLE,S_X,S_Y,S_Z})
    else $error("Illegal state encoding");

  // Reset behavior
  assert property (@cb dut.reset |-> (dut.current_state==S_IDLE
                                   && !dut.product_X_selected
                                   && !dut.product_Y_selected
                                   && !dut.product_Z_selected
                                   && !dut.dispensed))
    else $error("Reset did not clear to IDLE/zero outputs");

  // Output one-hot-0 and decode must reflect current_state
  assert property (@cb $onehot0({dut.product_X_selected, dut.product_Y_selected, dut.product_Z_selected}))
    else $error("Selection outputs not onehot0");
  assert property (@cb dut.product_X_selected == (dut.current_state==S_X))
    else $error("product_X_selected/state mismatch");
  assert property (@cb dut.product_Y_selected == (dut.current_state==S_Y))
    else $error("product_Y_selected/state mismatch");
  assert property (@cb dut.product_Z_selected == (dut.current_state==S_Z))
    else $error("product_Z_selected/state mismatch");

  // Priority and next-state function (A > B > C) from any state
  assert property (@cb dut.button_A |=> (dut.current_state==S_X))
    else $error("A priority to X violated");
  assert property (@cb (!dut.button_A && dut.button_B) |=> (dut.current_state==S_Y))
    else $error("B to Y violated");
  assert property (@cb (!dut.button_A && !dut.button_B && dut.button_C) |=> (dut.current_state==S_Z))
    else $error("C to Z violated");

  // IDLE holds with no buttons
  assert property (@cb (dut.current_state==S_IDLE && !dut.button_A && !dut.button_B && !dut.button_C) |=> (dut.current_state==S_IDLE))
    else $error("IDLE did not hold with no inputs");

  // Selected states: dispense returns to IDLE; otherwise hold with no inputs
  assert property (@cb (dut.current_state inside {S_X,S_Y,S_Z}
                        && !dut.button_A && !dut.button_B && !dut.button_C && dut.dispense) |=> (dut.current_state==S_IDLE))
    else $error("Dispense did not return to IDLE");
  assert property (@cb (dut.current_state==S_X && !dut.button_A && !dut.button_B && !dut.button_C && !dut.dispense) |=> (dut.current_state==S_X))
    else $error("X did not hold");
  assert property (@cb (dut.current_state==S_Y && !dut.button_A && !dut.button_B && !dut.button_C && !dut.dispense) |=> (dut.current_state==S_Y))
    else $error("Y did not hold");
  assert property (@cb (dut.current_state==S_Z && !dut.button_A && !dut.button_B && !dut.button_C && !dut.dispense) |=> (dut.current_state==S_Z))
    else $error("Z did not hold");

  // Dispensed handshake expectation (intent check; flags current RTL bug)
  assert property (@cb (dut.current_state inside {S_X,S_Y,S_Z}
                        && !dut.button_A && !dut.button_B && !dut.button_C && dut.dispense) |=> dut.dispensed)
    else $error("Dispense not acknowledged by dispensed");
  assert property (@cb dut.dispensed |=> !dut.dispensed)
    else $error("dispensed did not deassert after a pulse");
  assert property (@cb dut.dispensed |-> $past(dut.dispense))
    else $error("dispensed asserted without a dispense request");

  // Functional coverage
  cover property (@cb dut.current_state==S_IDLE ##1 dut.button_A
                       ##1 dut.current_state==S_X ##1 dut.dispense ##1 dut.current_state==S_IDLE);
  cover property (@cb dut.current_state==S_IDLE ##1 (!dut.button_A && dut.button_B)
                       ##1 dut.current_state==S_Y ##1 dut.dispense ##1 dut.current_state==S_IDLE);
  cover property (@cb dut.current_state==S_IDLE ##1 (!dut.button_A && !dut.button_B && dut.button_C)
                       ##1 dut.current_state==S_Z ##1 dut.dispense ##1 dut.current_state==S_IDLE);
  // Priority corner cases
  cover property (@cb dut.current_state==S_IDLE ##1 (dut.button_A && dut.button_B) ##1 dut.current_state==S_X);
  cover property (@cb dut.current_state==S_IDLE ##1 (dut.button_A && dut.button_C) ##1 dut.current_state==S_X);
  cover property (@cb dut.current_state==S_IDLE ##1 (!dut.button_A && dut.button_B && dut.button_C) ##1 dut.current_state==S_Y);

endmodule

bind vending_machine vending_machine_sva vm_sva();