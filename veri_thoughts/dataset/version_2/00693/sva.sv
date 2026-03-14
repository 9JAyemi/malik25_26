module shift_register_sva (
  input logic clk,
  input logic reset,
  input logic load,
  input logic [7:0] data_in,
  input logic [7:0] data_out
);

  ///// Reset behavior /////
  // While reset is asserted low, data_out must be zero.
  reset_clears_output: assert property (
    @(posedge clk) !reset |-> (data_out == 8'b0)
  );

  ///// Load behavior /////
  // When load is high, data_out updates to data_in in the same cycle.
  load_updates_immediately: assert property (
    @(posedge clk) disable iff (!reset) load |-> (data_out == data_in)
  );

  ///// Rotate behavior when not loading /////
  // When load is low, data_out rotates left by one bit from the previous value.
  rotate_one_step_vector: assert property (
    @(posedge clk) disable iff (!reset) !load |-> (data_out == { $past(data_out[6:0]), $past(data_out[7]) })
  );

  // Bit 7 takes previous bit 6 when not loading.
  rotate_bit7_from6: assert property (
    @(posedge clk) disable iff (!reset) !load |-> (data_out[7] == $past(data_out[6]))
  );

  // Bit 0 takes previous bit 7 when not loading.
  rotate_bit0_from7: assert property (
    @(posedge clk) disable iff (!reset) !load |-> (data_out[0] == $past(data_out[7]))
  );

  // Eight consecutive rotates return data_out to its value from eight cycles earlier.
  rotate_eight_cycle_identity: assert property (
    @(posedge clk) disable iff (!reset) (!load)[*8] |-> (data_out == $past(data_out, 8))
  );

  ///// Post-reset first-cycle behavior /////
  // On the first cycle after reset deasserts with no load, data_out remains zero.
  first_cycle_after_reset_no_load_zero: assert property (
    @(posedge clk) $rose(reset) && !load |-> (data_out == 8'b0)
  );

  // On the first cycle after reset deasserts with load, data_out equals data_in.
  first_cycle_after_reset_with_load_loads: assert property (
    @(posedge clk) $rose(reset) && load |-> (data_out == data_in)
  );

endmodule