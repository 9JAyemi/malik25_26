// SVA for sky130_fd_sc_ls__a31o: X = (A1 & A2 & A3) | B1
// Bind these assertions to the cell module

module sky130_fd_sc_ls__a31o_assert (
  input logic A1, A2, A3, B1,
  input logic X
);

  // Functional equivalence with 4-state semantics; use ##0 to avoid race with comb updates
  property p_func_eq;
    @(A1 or A2 or A3 or B1 or X)
      1 |-> ##0 (X === (B1 | (A1 & A2 & A3)));
  endproperty
  assert property (p_func_eq)
    else $error("a31o func mismatch: X != B1 | (A1 & A2 & A3)");

  // If all inputs are known, output must be known (no X/Z propagation when determinable)
  property p_known_out_when_known_in;
    @(A1 or A2 or A3 or B1 or X)
      !$isunknown({A1,A2,A3,B1}) |-> ##0 !$isunknown(X);
  endproperty
  assert property (p_known_out_when_known_in)
    else $error("a31o X is X/Z while inputs are all known");

  // Dominating value checks (useful 4-state corner constraints)
  // B1=1 forces X=1
  assert property (@(A1 or A2 or A3 or B1 or X) (B1 === 1) |-> ##0 (X === 1))
    else $error("a31o: B1=1 should force X=1");
  // B1=0 and any A=0 forces X=0
  assert property (@(A1 or A2 or A3 or B1 or X) (B1 === 0 && (A1===0 || A2===0 || A3===0)) |-> ##0 (X === 0))
    else $error("a31o: B1=0 with any A=0 should force X=0");
  // B1=0 and all A=1 forces X=1
  assert property (@(A1 or A2 or A3 or B1 or X) (B1 === 0 && A1===1 && A2===1 && A3===1) |-> ##0 (X === 1))
    else $error("a31o: B1=0 and A1=A2=A3=1 should force X=1");

  // Minimal toggle coverage on output
  cover property (@(A1 or A2 or A3 or B1 or X) $rose(X));
  cover property (@(A1 or A2 or A3 or B1 or X) $fell(X));

  // Functional full coverage: hit all 16 input combinations and observe the correct X
  genvar i;
  for (i = 0; i < 16; i++) begin : gen_minterm_cov
    localparam bit exp = (i[3] | (i[2] & i[1] & i[0])); // {B1,A3,A2,A1} -> expected X
    cover property (@(A1 or A2 or A3 or B1 or X)
      ##0 ({B1,A3,A2,A1} == i[3:0]) && (X === exp));
  end

endmodule

// Bind to all instances of the cell
bind sky130_fd_sc_ls__a31o sky130_fd_sc_ls__a31o_assert a31o_sva_bind (.*);