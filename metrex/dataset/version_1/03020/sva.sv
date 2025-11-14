// SVA for four_bit_adder
// Bind this checker to the DUT instance to verify and cover behavior.

module four_bit_adder_sva (
  input logic [3:0] a,
  input logic [3:0] b,
  input logic [3:0] sum
);

  // Helper: full-precision sum for overflow/wrap reasoning
  let ext_sum = {1'b0,a} + {1'b0,b};

  // Correctness when inputs are known; output must be known and equal to a+b (mod 16)
  assert property (@(a or b or sum)
    !$isunknown({a,b}) |-> (! $isunknown(sum) && sum == ext_sum[3:0])
  );

  // Output should not change unless inputs change (combinational purity)
  assert property (@(a or b or sum)
    $changed(sum) |-> ($changed(a) || $changed(b))
  );

  // If inputs are stable, output must be stable
  assert property (@(a or b or sum)
    $stable({a,b}) |-> $stable(sum)
  );

  // Identity properties
  assert property (@(a or b or sum)
    (a == 4'd0 && !$isunknown(b)) |-> (sum == b)
  );
  assert property (@(a or b or sum)
    (b == 4'd0 && !$isunknown(a)) |-> (sum == a)
  );

  // Monotonicity on +1 step of b with a held constant (wrap-aware)
  assert property (@(a or b or sum)
    !$isunknown({a,b,sum}) && $stable(a) && (b == $past(b)+4'd1)
    |-> (sum == $past(sum)+4'd1)
  );

  // Feature coverage
  cover property (@(a or b or sum) ext_sum[4]);      // overflow seen
  cover property (@(a or b or sum) !ext_sum[4]);     // no overflow
  cover property (@(a or b or sum) a == 4'h0);
  cover property (@(a or b or sum) b == 4'h0);
  cover property (@(a or b or sum) a == 4'hF);
  cover property (@(a or b or sum) b == 4'hF);
  cover property (@(a or b or sum) sum == 4'h0);
  cover property (@(a or b or sum) sum == 4'hF);

  // Compact full-value coverage of inputs and outputs
  covergroup cg_ab_sum @(a or b or sum);
    coverpoint a { bins all[] = {[0:15]}; }
    coverpoint b { bins all[] = {[0:15]}; }
    cross a, b;
    coverpoint sum { bins all[] = {[0:15]}; }
  endgroup
  cg_ab_sum cg_i = new;

endmodule

bind four_bit_adder four_bit_adder_sva sva_i (.*);