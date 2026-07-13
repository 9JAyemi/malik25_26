module binary_counter_sva (
  input logic clk,
  input logic reset,
  input logic [2:0] out
);

  // Reset drives next out to 000 on the following clock.
  check_reset_clears_next: assert property (
    @(posedge clk) reset |=> (out == 3'b000)
  );

  // 000 -> 001 when not in reset.
  check_count_000_to_001: assert property (
    @(posedge clk) disable iff (reset) (out == 3'b000) |=> (out == 3'b001)
  );

  // 001 -> 010 when not in reset.
  check_count_001_to_010: assert property (
    @(posedge clk) disable iff (reset) (out == 3'b001) |=> (out == 3'b010)
  );

  // 010 -> 011 when not in reset.
  check_count_010_to_011: assert property (
    @(posedge clk) disable iff (reset) (out == 3'b010) |=> (out == 3'b011)
  );

  // 011 -> 100 when not in reset.
  check_count_011_to_100: assert property (
    @(posedge clk) disable iff (reset) (out == 3'b011) |=> (out == 3'b100)
  );

  // 100 -> 101 when not in reset.
  check_count_100_to_101: assert property (
    @(posedge clk) disable iff (reset) (out == 3'b100) |=> (out == 3'b101)
  );

  // 101 -> 110 when not in reset.
  check_count_101_to_110: assert property (
    @(posedge clk) disable iff (reset) (out == 3'b101) |=> (out == 3'b110)
  );

  // 110 -> 000 when not in reset.
  check_count_110_to_000: assert property (
    @(posedge clk) disable iff (reset) (out == 3'b110) |=> (out == 3'b000)
  );

  // Default case: 111 -> 000 when not in reset.
  check_default_111_to_000: assert property (
    @(posedge clk) disable iff (reset) (out == 3'b111) |=> (out == 3'b000)
  );

endmodule