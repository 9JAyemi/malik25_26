// SVA for up_down_counter + binary_to_bcd_converter via top-level bind
// Focused, high-quality checks with essential coverage.

module top_module_sva (
  input  logic        clk,
  input  logic        up_down,
  input  logic        load,
  input  logic [3:0]  binary,
  input  logic [3:0]  count,
  input  logic [3:0]  BCD_HIGH,
  input  logic [3:0]  BCD_LOW
);

  // Establish a valid past-sample window (no explicit reset in DUT)
  logic initdone;
  initial initdone = 1'b0;
  always @(posedge clk) initdone <= 1'b1;

  default clocking cb @(posedge clk); endclocking
  default disable iff (!initdone);

  // Controls should be known
  assert property (!$isunknown({load, up_down})))
    else $error("X/Z on control inputs");

  // Counter next-state behavior
  assert property (load |=> count == $past(binary)))
    else $error("Load behavior mismatch");

  assert property (!load && up_down |=> count == ($past(count)+4'd1)[3:0]))
    else $error("Increment behavior mismatch");

  assert property (!load && !up_down |=> count == ($past(count)-4'd1)[3:0]))
    else $error("Decrement behavior mismatch");

  // Counter should not be X after first cycle
  assert property (!$isunknown(count)))
    else $error("X/Z on count");

  // Converter correctness (combinational relation to count)
  assert property (BCD_HIGH == (count/4'd10) && BCD_LOW == (count%4'd10)))
    else $error("BCD conversion mismatch");

  // Converter range checks
  assert property (BCD_HIGH inside {[4'd0:4'd1]} && BCD_LOW inside {[4'd0:4'd9]}))
    else $error("BCD range invalid");

  // Converter case refinements
  assert property ((count <= 4'd9)  |-> (BCD_HIGH == 4'd0 && BCD_LOW == count)))
    else $error("BCD low range case mismatch");
  assert property ((count >= 4'd10) |-> (BCD_HIGH == 4'd1 && BCD_LOW == (count-4'd10))))
    else $error("BCD high range case mismatch");

  // Key functional coverage
  // Load has priority over up_down
  cover property (load && up_down ##1 (count == $past(binary)));

  // Wrap-around on increment: F -> 0
  cover property ((!load && up_down && count == 4'hF) ##1 (count == 4'h0));

  // Wrap-around on decrement: 0 -> F
  cover property ((!load && !up_down && count == 4'h0) ##1 (count == 4'hF));

  // Exercise both up and down paths with a load in between
  cover property (load ##1 (!load && up_down) ##1 (!load && !up_down));

  // Exercise both BCD ranges
  cover property (count inside {[4'd0:4'd9]}  && BCD_HIGH == 4'd0);
  cover property (count inside {[4'd10:4'd15]} && BCD_HIGH == 4'd1);

endmodule

bind top_module top_module_sva sva (
  .clk      (clk),
  .up_down  (up_down),
  .load     (load),
  .binary   (binary),
  .count    (count),
  .BCD_HIGH (BCD_HIGH),
  .BCD_LOW  (BCD_LOW)
);