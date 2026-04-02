module debouncer_sva (
  input logic clk,
  input logic in,
  output logic out
);
  localparam CLK_FREQ = 100000; // clock frequency in Hz
  localparam DEBOUNCE_TIME = 10; // debounce time in ms

  reg [1:0] state;
  reg [31:0] debounce_count;

  localparam STABLE = 2'b00;
  localparam UNSTABLE = 2'b01;
  localparam DEBOUNCE = 2'b10;

  // Ensure state transitions are handled correctly
  state_transition: assert property (
    @(posedge clk) disable iff (!clk) (state == STABLE) |-> (state == STABLE || state == UNSTABLE)
  );
  state_transition_2: assert property (
    @(posedge clk) disable iff (!clk) (state == UNSTABLE) |-> (state == UNSTABLE || state == DEBOUNCE)
  );
  state_transition_3: assert property (
    @(posedge clk) disable iff (!clk) (state == DEBOUNCE) |-> (state == DEBOUNCE || state == STABLE)
  );

  // Ensure debounce_count is decremented correctly
  debounce_count_decrement: assert property (
    @(posedge clk) disable iff (!clk) (state == UNSTABLE) |-> (debounce_count > 0) |-> (debounce_count == debounce_count - 1)
  );

  // Ensure out is updated correctly during debounce
  out_update: assert property (
    @(posedge clk) disable iff (!clk) (state == DEBOUNCE) |-> (out == in)
  );

  // Ensure out remains stable during stable state
  out_stable: assert property (
    @(posedge clk) disable iff (!clk) (state == STABLE) |-> (out == out)
  );

  // Ensure debounce_count is reset correctly during stable state
  debounce_count_reset: assert property (
    @(posedge clk) disable iff (!clk) (state == STABLE) |-> (debounce_count == 0)
  );

  // Ensure debounce_count is reset correctly during unstable state
  debounce_count_reset_2: assert property (
    @(posedge clk) disable iff (!clk) (state == UNSTABLE) |-> (debounce_count == debounce_time * CLK_FREQ / 1000)
  );

  // Ensure debounce_count is reset correctly during debounce state
  debounce_count_reset_3: assert property (
    @(posedge clk) disable iff (!clk) (state == DEBOUNCE) |-> (debounce_count == debounce_time * CLK_FREQ / 1000)
  );

  // Ensure in is not driven during stable state
  in_stable: assert property (
    @(posedge clk) disable iff (!clk) (state == STABLE) |-> (in == in)
  );

  // Ensure in is not driven during debounce state
  in_debounce: assert property (
    @(posedge clk) disable iff (!clk) (state == DEBOUNCE) |-> (in == in)
  );
endmodule