// SVA checker for simple_adder
// Bind this to the DUT instance(s).
module simple_adder_sva (
  input logic [3:0] a,
  input logic [3:0] b,
  input logic [4:0] sum
);

  // Core functional check (clockless, event-driven)
  // Use ##0 to evaluate after combinational propagation.
  assert property (@(a or b or sum) !$isunknown({a,b,sum}))
    else $error("X/Z on inputs/outputs: a=%h b=%h sum=%h", a, b, sum);

  assert property (@(a or b or sum) 1'b1 |-> ##0 (sum == ({1'b0,a} + {1'b0,b})))
    else $error("Adder mismatch: a=%h b=%h exp=%h sum=%h",
                a, b, ({1'b0,a}+{1'b0,b}), sum);

  // Optional: carry bit matches expected carry-out (redundant but helpful)
  assert property (@(a or b or sum) 1'b1 |-> ##0 (sum[4] == ({1'b0,a}+{1'b0,b})[4]))
    else $error("Carry mismatch: a=%h b=%h exp_carry=%0b sum[4]=%0b",
                a, b, ({1'b0,a}+{1'b0,b})[4], sum[4]);

  // Coverage: key corners and carry/no-carry
  cover property (@(a or b or sum) (a==4'd0  && b==4'd0));
  cover property (@(a or b or sum) (a==4'hF && b==4'hF));
  cover property (@(a or b or sum) (a==4'd0  && b==4'hF));
  cover property (@(a or b or sum) (a==4'hF && b==4'd0));
  cover property (@(a or b or sum) ##0 (sum[4]==1'b0)); // no carry
  cover property (@(a or b or sum) ##0 (sum[4]==1'b1)); // carry

endmodule

// Bind example:
// bind simple_adder simple_adder_sva sva(.a(a), .b(b), .sum(sum));