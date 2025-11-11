// SVA for reverse_data
// Quality-focused, concise checks and coverage

module reverse_data_sva;

  default clocking cb @(posedge clk); endclocking

  // Helper (matches DUT behavior: pass-through)
  function automatic [7:0] id8(input [7:0] din);
    id8 = {din[7],din[6],din[5],din[4],din[3],din[2],din[1],din[0]};
  endfunction

  // Synchronous reset drives zeros next cycle
  assert property (@(posedge clk) reset |=> (data_out == 8'h00 && counter == 4'h0));

  // When not matching, counter increments (mod-16) and data_out holds
  assert property (@(posedge clk) disable iff (reset)
                   $past(!reset && counter != control)
                   |-> (counter == $past(counter + 4'h1) && data_out == $past(data_out)));

  // When matching, counter resets and data_out updates to prior data_in
  assert property (@(posedge clk) disable iff (reset)
                   $past(!reset && counter == control)
                   |-> (counter == 4'h0 && data_out == id8($past(data_in))));

  // Output changes only if a match happened in the previous cycle
  assert property (@(posedge clk) disable iff (reset)
                   (data_out != $past(data_out)) |-> $past(!reset && counter == control));

  // Connectivity: data_out mirrors data_out_reg
  assert property (@(posedge clk) (data_out === data_out_reg));

  // No X/Z on key signals after reset released
  assert property (@(posedge clk) disable iff (reset)
                   !$isunknown({data_out, counter}));

  // Coverage: update event
  cover property (@(posedge clk) disable iff (reset)
                  $past(!reset && counter == control) && counter == 4'h0);

  // Coverage: increment wraps 15 -> 0 without match
  cover property (@(posedge clk) disable iff (reset)
                  $past(!reset && counter == 4'hF && counter != control) && counter == 4'h0);

  // Coverage: control==0 causes back-to-back updates
  cover property (@(posedge clk) disable iff (reset)
                  $past(!reset && control == 4'h0 && counter == control) && counter == 4'h0);

endmodule

bind reverse_data reverse_data_sva sva_inst();