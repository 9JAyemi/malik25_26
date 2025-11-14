// SVA for sky130_fd_sc_hd__a31o
// Checks exact truth table and covers key scenarios.

module sky130_fd_sc_hd__a31o_sva (
  input A1, input A2, input A3, input B1,
  input X
);

  let all1  = (A1===1'b1 && A2===1'b1 && A3===1'b1 && B1===1'b1);
  let all0  = (A1===1'b0 && A2===1'b0 && A3===1'b0 && B1===1'b0);
  let anyX  = $isunknown({A1,A2,A3,B1});
  let mixed = (!anyX) && !(all1 || all0);

  // Exact functional spec (concise, bi-directional)
  property p_spec;
    @(*) 1'b1 |-> ##0 (
         (all1 && (X===1'b1))
      || (all0 && (X===1'b0))
      || ((!all1 && !all0) && $isunknown(X))
    );
  endproperty
  assert property (p_spec);

  // Output should never be Z
  assert property (@(*) 1'b1 |-> ##0 (X !== 1'bz));

  // Coverage
  cover property (@(*) all1  && (X===1'b1));
  cover property (@(*) all0  && (X===1'b0));
  cover property (@(*) mixed && $isunknown(X));
  cover property (@(*) anyX  && $isunknown(X));

endmodule

bind sky130_fd_sc_hd__a31o sky130_fd_sc_hd__a31o_sva sva_i (.*);