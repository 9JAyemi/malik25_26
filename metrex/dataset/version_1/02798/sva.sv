// SVA for Bit_Counter
// Bind example:
// bind Bit_Counter Bit_Counter_sva #(.BIT_COUNTER_INIT(BIT_COUNTER_INIT)) i_sva (.*,.bit_counter(bit_counter),.counting(counting),.reset_bit_counter(reset_bit_counter));

module Bit_Counter_sva #(
  parameter int BIT_COUNTER_INIT = 31
)(
  input  logic       clk,
  input  logic       reset,
  input  logic       bit_clk_rising_edge,
  input  logic       bit_clk_falling_edge,
  input  logic       left_right_clk_rising_edge,
  input  logic       left_right_clk_falling_edge,
  input  logic [4:0] bit_counter,
  input  logic       counting,
  input  logic       reset_bit_counter
);

  // Combinational equivalence of the internal wire
  assert property (@(posedge clk)
    reset_bit_counter == (left_right_clk_rising_edge || left_right_clk_falling_edge))
    else $error("reset_bit_counter != OR(left_right edges)");

  // Synchronous reset behavior
  assert property (@(posedge clk)
    reset |-> ##1 (bit_counter == 5'd0 && counting == 1'b0))
    else $error("Sync reset failed");

  // Load on LR edge (when not reset)
  assert property (@(posedge clk) disable iff (reset)
    reset_bit_counter |-> ##1 (bit_counter == BIT_COUNTER_INIT[4:0] && counting == 1'b1))
    else $error("Load on reset_bit_counter failed");

  // Decrement on bit falling edge when counter != 0 and not LR reset
  assert property (@(posedge clk) disable iff (reset)
    (bit_clk_falling_edge && (bit_counter != 5'd0) && !reset_bit_counter)
      |-> ##1 (bit_counter == $past(bit_counter) - 5'd1))
    else $error("Decrement behavior failed");

  // Hold counter otherwise (no reset, no load, no qualifying decrement)
  assert property (@(posedge clk) disable iff (reset)
    (!reset_bit_counter && !(bit_clk_falling_edge && (bit_counter != 5'd0)))
      |-> ##1 (bit_counter == $past(bit_counter)))
    else $error("Counter unexpected change");

  // Deassert counting one cycle after zero-edge when not LR reset
  assert property (@(posedge clk) disable iff (reset)
    (bit_clk_falling_edge && (bit_counter == 5'd0) && !reset_bit_counter)
      |-> ##1 (counting == 1'b0))
    else $error("Counting did not deassert at zero-edge");

  // Hold counting otherwise (no reset, no zero-edge stop, no load)
  assert property (@(posedge clk) disable iff (reset)
    (!reset_bit_counter && !(bit_clk_falling_edge && (bit_counter == 5'd0)))
      |-> ##1 (counting == $past(counting)))
    else $error("Counting unexpected change");

  // Rising-edge of bit clock has no effect
  assert property (@(posedge clk) disable iff (reset)
    (bit_clk_rising_edge && !bit_clk_falling_edge && !reset_bit_counter)
      |-> ##1 (bit_counter == $past(bit_counter) && counting == $past(counting)))
    else $error("bit_clk_rising_edge affected state");

  // Safety: counter never exceeds INIT
  assert property (@(posedge clk) disable iff (reset)
    bit_counter <= BIT_COUNTER_INIT[4:0])
    else $error("bit_counter exceeded INIT");

  // Safety: if counting is 0 (and not in reset), counter must be 0
  assert property (@(posedge clk) disable iff (reset)
    (counting == 1'b0) |-> (bit_counter == 5'd0))
    else $error("counting=0 while counter!=0");

  // Coverage

  // See both LR edges trigger load
  cover property (@(posedge clk) disable iff (reset)
    left_right_clk_rising_edge && reset_bit_counter);
  cover property (@(posedge clk) disable iff (reset)
    left_right_clk_falling_edge && reset_bit_counter);

  // Load then eventually stop counting at zero-edge
  cover property (@(posedge clk) disable iff (reset)
    reset_bit_counter ##1 (bit_counter == BIT_COUNTER_INIT[4:0] && counting)
    ##[1:$] (bit_clk_falling_edge && (bit_counter == 5'd0) && !reset_bit_counter)
    ##1 (counting == 1'b0));

  // Reach counter==0 after a load (some number of fall edges)
  cover property (@(posedge clk) disable iff (reset)
    reset_bit_counter ##[1:$] (bit_counter == 5'd0));

endmodule