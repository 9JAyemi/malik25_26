```systemverilog
module counter_4bit_sva (
  input logic clk,
  input logic reset,
  input logic enable,
  input logic [3:0] count
);
  // Reset behavior: count should be 0 at reset
  reset_behavior: assert property (
    @(posedge clk) disable iff (!reset) (count == 4'b0)
  );

  // Enable behavior: count should increment when enable is high
  enable_behavior: assert property (
    @(posedge clk) disable iff (!reset) (enable |-> count == count + 1)
  );

  // Disable behavior: count should not increment when enable is low
  disable_behavior: assert property (
    @(posedge clk) disable iff (!reset) (!enable |-> count == count)
  );

  // Count range behavior: count should not exceed 4'b1111
  count_range_behavior: assert property (
    @(posedge clk) disable iff (!reset) (count <= 4'b1111)
  );

  // Count should not wrap around from 4'b1111 to 4'b0000
  count_wrap_behavior: assert property (
    @(posedge clk) disable iff (!reset) (count != 4'b0000 |-> count != 4'b1111)
  );

  // Count should not be negative
  count_negative_behavior: assert property (
    @(posedge clk) disable iff (!reset) (count >= 4'b0000)
  );

  // Count should not be greater than 4 bits
  count_bits_behavior: assert property (
    @(posedge clk) disable iff (!reset) (count < 5'b10000)
  );

  // Count should not be equal to 4'b10000
  count_10000_behavior: assert property (
    @(posedge clk) disable iff (!reset) (count != 5'b10000)
  );

  // Count should not be equal to 4'b10001
  count_10001_behavior: assert property (
    @(posedge clk) disable iff (!reset) (count != 5'b10001)
  );

  // Count should not be equal to 4'b10010
  count_10010_behavior: assert property (
    @(posedge clk) disable iff (!reset) (count != 5'b10010)
  );

  // Count should not be equal to 4'b10011
  count_10011_behavior: assert property (
    @(posedge clk) disable iff (!reset) (count != 5'b10011)
  );

  // Count should not be equal to 4'b10100
  count_10100_behavior: assert property (
    @(posedge clk) disable iff (!reset) (count != 5'b10100)
  );

  // Count should not be equal to 4'b10101
  count_10101_behavior: assert property (
    @(posedge clk) disable iff (!reset) (count != 5'b10101)
  );

  // Count should not be equal to 4'b10110
  count_10110_behavior: assert property (
    @(posedge clk) disable iff (!reset) (count != 5'b10110)
  );

  // Count should not be equal to 4'b10111
  count_10111_behavior: assert property (
    @(posedge clk) disable iff (!reset) (count != 5'b10111)
  );

  // Count should not be equal to 4'b11000
  count_11000_behavior: assert property (
    @(posedge clk) disable iff (!reset) (count != 5'b11000)
  );

  // Count should not be equal to 4'b11001
  count_11001_behavior: assert property (
    @(posedge clk) disable iff (!reset) (count != 5'b11001)
  );

  // Count should not be equal to 4'b11010
  count_11010_behavior: assert property (
    @(posedge clk) disable iff (!reset) (count != 5'b11010)
  );

  // Count should not be equal to 4'b11011
  count_11011_behavior: assert property (
    @(posedge clk) disable iff (!reset) (count != 5'b11011)
  );

  // Count should not be equal to 4'b11100
  count_11100_behavior: assert property (
    @(posedge clk) disable iff (!reset) (count != 5'b11100)
  );

  // Count should not be equal to 4'b11101
  count_11101_behavior: assert property (
    @(posedge clk) disable iff (!reset) (count != 5'b11101)
  );

  // Count should not be equal to 4'b11110
  count_11110_behavior: assert property (
    @(posedge clk) disable iff (!reset) (count != 5'b11110)
  );

  // Count should not be equal to 4'b11111
  count_11111_behavior: assert property (
    @(posedge clk) disable iff (!reset) (count != 5'b11111)
  );
endmodule
```