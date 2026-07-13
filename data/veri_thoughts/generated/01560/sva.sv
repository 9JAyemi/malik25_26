module binary_counter_sva (
  input logic clk,
  input logic reset,
  input logic [2:0] count,
  input logic enable
);

  // On reset, next cycle drives count=0 and enable=0.
  reset_next_outputs_zero: assert property (
    @(posedge clk) reset |=> (count == 3'b000) && (enable == 1'b0)
  );

  // From count=0, next is 1 and enable=0.
  next_from_0: assert property (
    @(posedge clk) disable iff (reset) (count == 3'b000) |=> (count == 3'b001) && (enable == 1'b0)
  );

  // From count=1, next is 2 and enable=0.
  next_from_1: assert property (
    @(posedge clk) disable iff (reset) (count == 3'b001) |=> (count == 3'b010) && (enable == 1'b0)
  );

  // From count=2, next is 3 and enable=0.
  next_from_2: assert property (
    @(posedge clk) disable iff (reset) (count == 3'b010) |=> (count == 3'b011) && (enable == 1'b0)
  );

  // From count=3, next is 4 and enable=0.
  next_from_3: assert property (
    @(posedge clk) disable iff (reset) (count == 3'b011) |=> (count == 3'b100) && (enable == 1'b0)
  );

  // From count=4, next is 5 and enable=0.
  next_from_4: assert property (
    @(posedge clk) disable iff (reset) (count == 3'b100) |=> (count == 3'b101) && (enable == 1'b0)
  );

  // From count=5, next is 0 and enable=1.
  next_from_5: assert property (
    @(posedge clk) disable iff (reset) (count == 3'b101) |=> (count == 3'b000) && (enable == 1'b1)
  );

  // From count=6, next is 7 and enable=0.
  next_from_6: assert property (
    @(posedge clk) disable iff (reset) (count == 3'b110) |=> (count == 3'b111) && (enable == 1'b0)
  );

  // From count=7, next is 0 and enable=0.
  next_from_7: assert property (
    @(posedge clk) disable iff (reset) (count == 3'b111) |=> (count == 3'b000) && (enable == 1'b0)
  );

  // Enable is a single-cycle pulse.
  enable_one_cycle_pulse: assert property (
    @(posedge clk) disable iff (reset) (enable == 1'b1) |=> (enable == 1'b0)
  );

  // When enable is 1, the count in that cycle is 0.
  enable_implies_count_zero: assert property (
    @(posedge clk) disable iff (reset) (enable == 1'b1) |-> (count == 3'b000)
  );

  // While count is 5, enable is 0 in that same cycle.
  count5_implies_enable_zero: assert property (
    @(posedge clk) disable iff (reset) (count == 3'b101) |-> (enable == 1'b0)
  );

endmodule