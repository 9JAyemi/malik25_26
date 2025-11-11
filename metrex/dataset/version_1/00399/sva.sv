// SVA for nfc_transmitter and nfc_receiver
// Bind these to the DUTs; no DUT/testbench changes required.

module nfc_transmitter_sva;
  default clocking cb @(posedge clk); endclocking

  // Counter increments every cycle (wraps naturally)
  assert property (!$isunknown($past(counter)) |-> counter == $past(counter) + 32'd1);

  // Local carrier_gen toggles every cycle
  assert property (!$isunknown($past(carrier_gen)) |-> carrier_gen == ~$past(carrier_gen));

  // en is a 1-cycle delayed copy of data_in
  assert property (!$isunknown($past(data_in)) |-> en == $past(data_in));

  // carrier_out reflects previous en gating and previous carrier_gen
  assert property (
    (!$isunknown($past(en)) && !$isunknown($past(carrier_gen)))
    |-> carrier_out == ($past(en) ? $past(carrier_gen) : 1'b0)
  );

  // Minimal functional coverage
  cover property ($rose(en));
  cover property ($fell(en));
  // When previously enabled, carrier_out should toggle each cycle (since carrier_gen toggles)
  cover property ($past(en) && carrier_out != $past(carrier_out));
  // When previously disabled, carrier_out must be 0
  cover property (!$past(en) && carrier_out == 1'b0);
endmodule

bind nfc_transmitter nfc_transmitter_sva nfc_transmitter_sva_inst();


module nfc_receiver_sva;
  default clocking cb @(posedge clk); endclocking

  // Counter increments every cycle (wraps naturally)
  assert property (!$isunknown($past(counter)) |-> counter == $past(counter) + 32'd1);

  // Local carrier_gen toggles every cycle
  assert property (!$isunknown($past(carrier_gen)) |-> carrier_gen == ~$past(carrier_gen));

  // prev_carrier_in tracks the previous cycle's carrier_in
  assert property (!$isunknown($past(carrier_in)) |-> prev_carrier_in == $past(carrier_in));

  // valid_out flags exactly when carrier_in changes from previous cycle
  assert property (
    (!$isunknown($past(carrier_in))) |-> (valid_out == (carrier_in != $past(carrier_in)))
  );

  // data_out equals previous carrier_gen when a change is detected; else 0
  assert property (
    (!$isunknown($past(carrier_in)) && !$isunknown($past(carrier_gen)))
    |-> data_out == ((carrier_in != $past(carrier_in)) ? $past(carrier_gen) : 1'b0)
  );

  // Minimal functional coverage
  cover property (valid_out);                    // detected at least one edge
  cover property (!valid_out);                   // stable cycle
  cover property (valid_out && data_out == 1'b1);
  cover property (valid_out && data_out == 1'b0);
endmodule

bind nfc_receiver nfc_receiver_sva nfc_receiver_sva_inst();