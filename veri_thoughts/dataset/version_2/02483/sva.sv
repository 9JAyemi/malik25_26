module CounterChainCore_sva (
  input logic        clock,
  input logic        reset,       // active-high synchronous reset
  input logic [9:0]  io_out_0,
  input logic [9:0]  io_out_1,
  input logic [9:0]  io_next_1,
  input logic        io_enable_0,
  input logic        io_done_0
);
  // On reset, io_out_0 becomes 0 on the next clock.
  reset_clears_out0_next: assert property (
    @(posedge clock) reset |=> (io_out_0 == 10'h0)
  );

  // Counter updates by +1 on prior enable, else holds (one-cycle step).
  check_counter_step_update: assert property (
    @(posedge clock) disable iff (reset)
      $past(!reset) |-> (io_out_0 == ($past(io_out_0) + ($past(io_enable_0) ? 10'h1 : 10'h0)))
  );

  // io_out_0 changes only if prior cycle had enable HIGH.
  check_change_requires_enable: assert property (
    @(posedge clock) disable iff (reset)
      ($past(!reset) && (io_out_0 != $past(io_out_0))) |-> $past(io_enable_0)
  );

  // io_done_0 equals comparison of next value to 9 (configured max).
  check_done_definition: assert property (
    @(posedge clock) disable iff (reset)
      io_done_0 == (((io_enable_0 ? (io_out_0 + 10'h1) : io_out_0) == 10'h9))
  );

  // io_out_1 is 1 when done, else 0.
  check_out1_maps_done: assert property (
    @(posedge clock) disable iff (reset)
      io_out_1 == (io_done_0 ? 10'h1 : 10'h0)
  );

  // io_next_1 is 2 when done, else 1.
  check_next1_maps_done: assert property (
    @(posedge clock) disable iff (reset)
      io_next_1 == (io_done_0 ? 10'h2 : 10'h1)
  );

  // io_next_1 always equals io_out_1 + 1.
  check_next1_eq_out1_plus1: assert property (
    @(posedge clock) disable iff (reset)
      io_next_1 == (io_out_1 + 10'h1)
  );
endmodule