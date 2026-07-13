module counter_3bit_sva (
  input logic clk,
  input logic reset,
  input logic enable,
  input logic [2:0] count
);

  // Synchronous reset drives count to 0 on the next cycle.
  reset_drives_zero: assert property (
    @(posedge clk) reset |-> (count == 3'b000)
  );

  // When enable is LOW, count holds its value.
  hold_when_enable_low: assert property (
    @(posedge clk) disable iff (reset) (!enable) |-> (count == $past(count))
  );

  // With enable HIGH and count==000, next is 001.
  trans_000_to_001: assert property (
    @(posedge clk) disable iff (reset) (enable && (count == 3'b000)) |-> (count == 3'b001)
  );

  // With enable HIGH and count==001, next is 010.
  trans_001_to_010: assert property (
    @(posedge clk) disable iff (reset) (enable && (count == 3'b001)) |-> (count == 3'b010)
  );

  // With enable HIGH and count==010, next is 011.
  trans_010_to_011: assert property (
    @(posedge clk) disable iff (reset) (enable && (count == 3'b010)) |-> (count == 3'b011)
  );

  // With enable HIGH and count==011, next is 100.
  trans_011_to_100: assert property (
    @(posedge clk) disable iff (reset) (enable && (count == 3'b011)) |-> (count == 3'b100)
  );

  // With enable HIGH and count==100, next is 101.
  trans_100_to_101: assert property (
    @(posedge clk) disable iff (reset) (enable && (count == 3'b100)) |-> (count == 3'b101)
  );

  // With enable HIGH and count==101, next is 110.
  trans_101_to_110: assert property (
    @(posedge clk) disable iff (reset) (enable && (count == 3'b101)) |-> (count == 3'b110)
  );

  // With enable HIGH and count==110, next is 000.
  trans_110_to_000: assert property (
    @(posedge clk) disable iff (reset) (enable && (count == 3'b110)) |-> (count == 3'b000)
  );

  // With enable HIGH and count==111, count holds (no case match).
  hold_111_when_enable_high: assert property (
    @(posedge clk) disable iff (reset) (enable && (count == 3'b111)) |-> (count == 3'b111)
  );

  // If count changes, the cause is prior reset or a valid enabled transition.
  change_has_valid_cause: assert property (
    @(posedge clk)
      (count != $past(count)) |-> (
        $past(reset) ||
        ($past(enable) && (
          ($past(count) == 3'b000 && count == 3'b001) ||
          ($past(count) == 3'b001 && count == 3'b010) ||
          ($past(count) == 3'b010 && count == 3'b011) ||
          ($past(count) == 3'b011 && count == 3'b100) ||
          ($past(count) == 3'b100 && count == 3'b101) ||
          ($past(count) == 3'b101 && count == 3'b110) ||
          ($past(count) == 3'b110 && count == 3'b000)
        ))
      )
  );

  // With enable HIGH and count not 111, count must change next cycle.
  change_when_enabled_from_valid_state: assert property (
    @(posedge clk) disable iff (reset) (enable && (count != 3'b111)) |-> (count != $past(count))
  );

endmodule