module counter_4bit_sync_reset_load_sva (
  input logic clk,
  input logic reset,
  input logic load,
  input logic [3:0] data_in,
  output logic [3:0] count
);
  ///// Synchronous Reset Behavior /////
  // At reset, the counter should be driven to 0.
  reset_to_zero: assert property (
    @(posedge clk) disable iff (!reset) reset |-> count == 4'b0
  );

  ///// Load Behavior /////
  // When load is asserted, the counter should be loaded with data_in.
  load_behavior: assert property (
    @(posedge clk) disable iff (!reset) load |-> count == data_in
  );

  ///// Counting Behavior /////
  // When neither reset nor load is asserted, the counter should increment by 1.
  counting_behavior: assert property (
    @(posedge clk) disable iff (!reset) !(reset | load) |-> count == count + 4'b1
  );
endmodule