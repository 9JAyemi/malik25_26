// SVA bind checker for comparator
module comparator_sva_checker (
  input logic [3:0] a,
  input logic [3:0] b,
  input logic       gt,
  input logic       lt,
  input logic       eq
);

  // Functional equivalence (only when inputs are known)
  assert property (@(a or b)
    !$isunknown({a,b}) |-> ((gt == (a > b)) && (lt == (a < b)) && (eq == (a == b)))
  );

  // Outputs are exactly one-hot
  assert property (@(a or b or gt or lt or eq)
    $onehot({gt,lt,eq})
  );

  // Outputs never X/Z
  assert property (@(gt or lt or eq)
    !$isunknown({gt,lt,eq})
  );

  // Coverage: all relation outcomes observed
  cover property (@(a or b) !$isunknown({a,b}) && (a > b) && gt);
  cover property (@(a or b) !$isunknown({a,b}) && (a < b) && lt);
  cover property (@(a or b) !$isunknown({a,b}) && (a == b) && eq);

  // Coverage: a couple of corner pairs
  cover property (@(a or b) (a==4'd0)  && (b==4'd15) && lt);
  cover property (@(a or b) (a==4'd15) && (b==4'd0)  && gt);

endmodule

// Bind into the DUT
bind comparator comparator_sva_checker u_comparator_sva_checker (
  .a(a), .b(b), .gt(gt), .lt(lt), .eq(eq)
);