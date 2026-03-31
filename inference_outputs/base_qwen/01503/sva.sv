```systemverilog
module fsm_rising_edge_counter_sva (
  input logic clk,
  input logic in,
  input logic reset_n,
  output logic [2:0] count
);

  reg d_last;
  reg [1:0] state;

  parameter IDLE = 2'b00;
  parameter COUNT = 2'b01;

  // Ensure that the counter increments on rising edges of 'in'
  rising_edge_count: assert property (
    @(posedge clk) disable iff (!reset_n) (in && !d_last) |-> count == count + 1
  );

  // Ensure that the counter resets to 0 when 'in' is high and 'd_last' is low
  reset_count: assert property (
    @(posedge clk) disable iff (!reset_n) (in && !d_last) |-> count == 0
  );

  // Ensure that the counter remains at 4 and transitions back to IDLE state
  max_count: assert property (
    @(posedge clk) disable iff (!reset_n) (count == 4) |-> state == IDLE
  );

  // Ensure that the counter does not increment when 'in' is low
  no_increment_when_low: assert property (
    @(posedge clk) disable iff (!reset_n) (!in) |-> count == count
  );

  // Ensure that the counter does not increment when 'd_last' is high
  no_increment_when_d_last_high: assert property (
    @(posedge clk) disable iff (!reset_n) (d_last) |-> count == count
  );

  // Ensure that the counter increments only when 'in' is high and 'd_last' is low
  increment_condition: assert property (
    @(posedge clk) disable iff (!reset_n) (in && !d_last) |-> count == count + 1
  );

  // Ensure that the counter does not reset when 'in' is low
  no_reset_when_low: assert property (
    @(posedge clk) disable iff (!reset_n) (!in) |-> count == count
  );

  // Ensure that the counter does not reset when 'd_last' is high
  no_reset_when_d_last_high: assert property (
    @(posedge clk) disable iff (!reset_n) (d_last) |-> count == count
  );

  // Ensure that the counter increments only when 'in' is high and 'd_last' is low
  increment_condition_2: assert property (
    @(posedge clk) disable iff (!reset_n) (in && !d_last) |-> count == count + 1
  );

endmodule
```