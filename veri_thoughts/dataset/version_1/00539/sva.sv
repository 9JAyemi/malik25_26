// SVA for mult_by_3
// Bind this module to the DUT: bind mult_by_3 mult_by_3_sva sva(.x(x), .y(y));

module mult_by_3_sva (
  input logic [3:0] x,
  input logic [5:0] y
);

  // Sample on any change; use ##0 to evaluate after combinational settling
  // No X/Z on interface
  assert property (@(x or y) 1 |-> ##0 (!$isunknown(x) && !$isunknown(y)))
    else $error("X/Z detected: x=%b y=%b", x, y);

  // Functional correctness: y == 3*x with proper zero-extension
  assert property (@(x or y) 1 |-> ##0 (y == ({2'b0,x} + ({2'b0,x} << 1))))
    else $error("y != 3*x: x=%0d y=%0d exp=%0d", x, y, {2'b0,x}+({2'b0,x}<<1));

  // Range and simple arithmetic invariants
  assert property (@(x or y) 1 |-> ##0 (y <= 6'd45))
    else $error("Range violation: y=%0d (>45) for x=%0d", y, x);

  assert property (@(x or y) 1 |-> ##0 (y[0] == x[0]))
    else $error("LSB mismatch: x[0]=%0b y[0]=%0b", x[0], y[0]);

  assert property (@(x or y) 1 |-> ##0 ((y % 3) == 0))
    else $error("Non-multiple-of-3 output: x=%0d y=%0d", x, y);

  // Coverage: hit all input values and their correct mapped outputs
  genvar i;
  for (i = 0; i < 16; i++) begin : C_ALL_X
    cover property (@(x) ##0 (x == i[3:0] && y == (i*3)[5:0]));
  end

  // Corner coverage
  cover property (@(x) ##0 (x == 4'd0 && y == 6'd0));
  cover property (@(x) ##0 (x == 4'd15 && y == 6'd45));

endmodule

// Example bind (place in a package or a separate bind file as appropriate):
// bind mult_by_3 mult_by_3_sva sva(.x(x), .y(y));