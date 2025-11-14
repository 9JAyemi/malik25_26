// SVA for my_module: X = (A1 | A2) & B1 & VPWR
module my_module_sva (input A1, A2, B1, VPWR, X);

  // Functional equivalence when inputs are known
  property p_func_equiv_known;
    @(A1 or A2 or B1 or VPWR or X)
      !$isunknown({A1,A2,B1,VPWR}) |-> (X == ((A1 | A2) & B1 & VPWR));
  endproperty
  assert property (p_func_equiv_known);

  // Deterministic output when inputs are known (no X/Z on X)
  property p_no_x_on_known_inputs;
    @(A1 or A2 or B1 or VPWR)
      !$isunknown({A1,A2,B1,VPWR}) |-> !$isunknown(X);
  endproperty
  assert property (p_no_x_on_known_inputs);

  // Zero-dominance invariants
  assert property (@(A1 or A2 or B1 or VPWR or X) (VPWR === 1'b0) |-> (X === 1'b0));
  assert property (@(A1 or A2 or B1 or VPWR or X) (B1   === 1'b0) |-> (X === 1'b0));
  assert property (@(A1 or A2 or B1 or VPWR or X) ((A1 === 1'b0) && (A2 === 1'b0)) |-> (X === 1'b0));

  // One assertion when all enables are 1
  assert property (@(A1 or A2 or B1 or VPWR or X)
                   (VPWR === 1'b1 && B1 === 1'b1 && (A1 === 1'b1 || A2 === 1'b1)) |-> (X === 1'b1));

  // Output rise implies all enables asserted (with known inputs)
  assert property (@(A1 or A2 or B1 or VPWR or X)
                   ($rose(X) && !$isunknown({A1,A2,B1,VPWR})) |-> (VPWR && B1 && (A1 || A2)));

  // Output fall implies at least one disabling condition (with known inputs)
  assert property (@(A1 or A2 or B1 or VPWR or X)
                   ($fell(X) && !$isunknown({A1,A2,B1,VPWR})) |-> (!VPWR || !B1 || (!A1 && !A2)));

  // Minimal, meaningful coverage
  cover property (@(A1 or A2 or B1 or VPWR or X) (VPWR && B1 &&  A1 && !A2 && X));
  cover property (@(A1 or A2 or B1 or VPWR or X) (VPWR && B1 && !A1 &&  A2 && X));
  cover property (@(A1 or A2 or B1 or VPWR or X) (!VPWR && (X === 1'b0)));
  cover property (@(A1 or A2 or B1 or VPWR or X) (VPWR && B1 && !(A1||A2) && (X === 1'b0)));
  cover property (@(A1 or A2 or B1 or VPWR or X) $rose(X));
  cover property (@(A1 or A2 or B1 or VPWR or X) $fell(X));

endmodule

bind my_module my_module_sva sva_inst (.*);