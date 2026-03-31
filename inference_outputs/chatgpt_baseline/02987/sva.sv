module calculator_sva (
  input  logic signed [7:0] a,
  input  logic signed [7:0] b,
  input  logic              op,
  input  logic              clk,
  input  logic signed [7:0] result,
  input  logic              overflow
);
  // Clock: clk (posedge). No reset present in RTL.
  // Logic: mixed — result is combinational; overflow is registered each clk.

  ///// Result computation /////
  // When op==0, result equals a + b (combinational).
  result_add_correct: assert property (
    @(posedge clk) (op == 1'b0) |-> (result == (a + b))
  );

  // When op==1, result equals a - b (combinational).
  result_sub_correct: assert property (
    @(posedge clk) (op == 1'b1) |-> (result == (a - b))
  );

  // If inputs are unchanged across a cycle, result must be unchanged.
  stable_result_when_inputs_stable: assert property (
    @(posedge clk) ((a == $past(a)) && (b == $past(b)) && (op == $past(op))) |-> (result == $past(result))
  );

  // If op rises (a,b stable), previous result was a+b and current result is a-b.
  result_switch_on_op_rise: assert property (
    @(posedge clk) ($past(op) == 1'b0 && op == 1'b1 && a == $past(a) && b == $past(b)) |-> ((result == (a - b)) && ($past(result) == ($past(a) + $past(b))))
  );

  // If op falls (a,b stable), previous result was a-b and current result is a+b.
  result_switch_on_op_fall: assert property (
    @(posedge clk) ($past(op) == 1'b1 && op == 1'b0 && a == $past(a) && b == $past(b)) |-> ((result == (a + b)) && ($past(result) == ($past(a) - $past(b))))
  );

  ///// Overflow computation (registered) /////
  // On the next cycle, overflow must be 1 when the RTL's overflow condition holds.
  overflow_set_when_condition: assert property (
    @(posedge clk)
      (
        ((result[7] == 1'b1) && (op == 1'b0) && (a[7] == 1'b1) && (b[7] == 1'b1)) ||
        ((result[7] == 1'b1) && (op == 1'b1) && (a[7] == 1'b0) && (b[7] == 1'b1)) ||
        ((result[7] == 1'b0) && (op == 1'b1) && (a[7] == 1'b1) && (b[7] == 1'b0))
      ) |=> (overflow == 1'b1)
  );

  // On the next cycle, overflow must be 0 when the RTL's overflow condition does not hold.
  overflow_clear_when_not_condition: assert property (
    @(posedge clk)
      !(
        ((result[7] == 1'b1) && (op == 1'b0) && (a[7] == 1'b1) && (b[7] == 1'b1)) ||
        ((result[7] == 1'b1) && (op == 1'b1) && (a[7] == 1'b0) && (b[7] == 1'b1)) ||
        ((result[7] == 1'b0) && (op == 1'b1) && (a[7] == 1'b1) && (b[7] == 1'b0))
      ) |=> (overflow == 1'b0)
  );

  // After the first cycle, overflow is always a known 0/1 (registered each clk).
  overflow_binary_after_first_cycle: assert property (
    @(posedge clk) $past(1'b1) |-> (overflow inside {1'b0, 1'b1})
  );

  // If op and MSBs used by the RTL overflow logic are unchanged across a cycle, overflow holds its value on the next cycle.
  overflow_stable_when_signs_stable: assert property (
    @(posedge clk)
      ((a[7] == $past(a[7])) && (b[7] == $past(b[7])) && (result[7] == $past(result[7])) && (op == $past(op)))
      |=> (overflow == $past(overflow))
  );

endmodule