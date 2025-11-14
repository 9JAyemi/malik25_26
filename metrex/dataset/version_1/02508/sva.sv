// SVA for bitwise_operation
// Bindable, concise, and focused on correctness and meaningful coverage.

module bitwise_operation_sva #(parameter WIDTH=16)
(
  input logic [WIDTH-1:0] x, y, out,
  input logic [WIDTH-1:0] and_n, or_n, not_n, xor_n,
  input logic [2:0]       func
);

  // Functional correctness of internal nets
  assert property (@(x or y or and_n) and_n == (x & y));
  assert property (@(x or y or or_n ) or_n  == (x | y));
  assert property (@(x       or not_n) not_n == ~x     );
  assert property (@(x or y or xor_n) xor_n  == (x ^ y));

  // func is constant 3'b010 (as coded)
  assert property (@(x or y or func) func === 3'b010);

  // Output equals NOT-x and matches not_n
  assert property (@(x or out or not_n) out == ~x && out == not_n);

  // Output independence from y (with x stable)
  assert property (@(x or y or out) disable iff ($isunknown({x,y,out}))
                   $changed(y) && $stable(x) |-> $stable(out));

  // No X/Z propagation when inputs are known
  assert property (@(x or y or out ) (!$isunknown({x,y})) |-> !$isunknown(out ));
  assert property (@(x or y or and_n) (!$isunknown({x,y})) |-> !$isunknown(and_n));
  assert property (@(x or y or or_n ) (!$isunknown({x,y})) |-> !$isunknown(or_n ));
  assert property (@(x       or not_n) (!$isunknown(x    )) |-> !$isunknown(not_n));
  assert property (@(x or y or xor_n) (!$isunknown({x,y})) |-> !$isunknown(xor_n));

  // Coverage: extremes, toggles, and exercising internal nets
  cover property (@(x or y) x == {WIDTH{1'b0}} && out == {WIDTH{1'b1}});
  cover property (@(x or y) x == {WIDTH{1'b1}} && out == {WIDTH{1'b0}});
  cover property (@(x or y) $onehot0(x ^ $past(x)));               // single-bit toggle on x
  cover property (@(x or y) $changed(y) && $stable(x));            // y-only changes observed
  cover property (@(x or y) and_n != {WIDTH{1'b0}});
  cover property (@(x or y) or_n  != {WIDTH{1'b0}});
  cover property (@(x or y) xor_n != {WIDTH{1'b0}});

endmodule

// Bind into the DUT to observe internal nets without modifying RTL
bind bitwise_operation bitwise_operation_sva #(.WIDTH(16)) bitwise_operation_sva_i (
  .x(x), .y(y), .out(out),
  .and_n(and_n), .or_n(or_n), .not_n(not_n), .xor_n(xor_n),
  .func(func)
);