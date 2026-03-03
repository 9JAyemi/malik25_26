// SVA for and_delayed
module and_delayed_sva (
  input  logic clk,
  input  logic a,
  input  logic b,
  input  logic out,
  input  logic delayed_a,
  input  logic delayed_b
);

  default clocking cb @ (posedge clk); endclocking

  logic past_valid;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // Stage registers must capture a/b exactly one cycle later
  assert property (past_valid && !$isunknown($past(a)) |-> delayed_a == $past(a))
    else $error("delayed_a != $past(a)");
  assert property (past_valid && !$isunknown($past(b)) |-> delayed_b == $past(b))
    else $error("delayed_b != $past(b)");

  // Output must be 1-cycle delayed AND of inputs
  assert property (past_valid && !$isunknown($past({a,b})) |-> out == ($past(a) & $past(b)))
    else $error("out != $past(a)&$past(b)");

  // Equivalent check via delayed stage values (NB-assignment semantics)
  assert property (past_valid && !$isunknown($past({delayed_a,delayed_b})) |-> out == ($past(delayed_a) & $past(delayed_b)))
    else $error("out != $past(delayed_a)&$past(delayed_b)");

  // No-X on out when past inputs were known
  assert property (past_valid && !$isunknown($past({a,b})) |-> !$isunknown(out))
    else $error("out is X/Z while past inputs were known");

  // Functional coverage
  cover property (past_valid && $past({a,b}) == 2'b11 && out); // AND=1 case
  cover property (past_valid && $past({a,b}) == 2'b10 && !out);
  cover property (past_valid && $past({a,b}) == 2'b01 && !out);
  cover property (past_valid && $past({a,b}) == 2'b00 && !out);

  cover property (past_valid && $rose(out));
  cover property (past_valid && $fell(out));

endmodule

bind and_delayed and_delayed_sva sva_i (.*);