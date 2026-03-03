// SVA for sky130_fd_sc_ms__a21bo
// Function: X = (~B1_N) | (A1 & A2)

module sky130_fd_sc_ms__a21bo_sva (
  input logic A1,
  input logic A2,
  input logic B1_N,
  input logic X
);

  // Functional equivalence (4-state safe, #0 to avoid race)
  always_comb begin
    assert (#0 (X === ((~B1_N) | (A1 & A2))))
      else $error("a21bo func mismatch: X=%b A1=%b A2=%b B1_N=%b", X, A1, A2, B1_N);
  end

  // Known output when inputs are known
  always_comb if (!$isunknown({A1,A2,B1_N})) begin
    assert (#0 ! $isunknown(X))
      else $error("a21bo: X unknown with known inputs");
  end

  // Deterministic forcing cases
  always_comb if (B1_N === 1'b0) begin
    assert (#0 X === 1'b1)
      else $error("a21bo: B1_N=0 must force X=1");
  end
  always_comb if (B1_N === 1'b1) begin
    assert (#0 X === (A1 & A2))
      else $error("a21bo: B1_N=1 implies X=A1&A2");
  end

  // Causality: X only changes when some input changes
  property x_changes_only_on_input_change;
    $changed(X) |-> ($changed(A1) or $changed(A2) or $changed(B1_N));
  endproperty
  a_x_change_src: assert property (@(A1 or A2 or B1_N or X) x_changes_only_on_input_change)
    else $error("a21bo: X changed without input change");

  // Truth-table coverage (all input minterms with expected X)
  cover property (@(A1 or A2 or B1_N or X)
    !$isunknown({A1,A2,B1_N}) && (A1==1'b0 && A2==1'b0 && B1_N==1'b0 && X==1'b1));
  cover property (@(A1 or A2 or B1_N or X)
    !$isunknown({A1,A2,B1_N}) && (A1==1'b0 && A2==1'b1 && B1_N==1'b0 && X==1'b1));
  cover property (@(A1 or A2 or B1_N or X)
    !$isunknown({A1,A2,B1_N}) && (A1==1'b1 && A2==1'b0 && B1_N==1'b0 && X==1'b1));
  cover property (@(A1 or A2 or B1_N or X)
    !$isunknown({A1,A2,B1_N}) && (A1==1'b1 && A2==1'b1 && B1_N==1'b0 && X==1'b1));
  cover property (@(A1 or A2 or B1_N or X)
    !$isunknown({A1,A2,B1_N}) && (A1==1'b0 && A2==1'b0 && B1_N==1'b1 && X==1'b0));
  cover property (@(A1 or A2 or B1_N or X)
    !$isunknown({A1,A2,B1_N}) && (A1==1'b0 && A2==1'b1 && B1_N==1'b1 && X==1'b0));
  cover property (@(A1 or A2 or B1_N or X)
    !$isunknown({A1,A2,B1_N}) && (A1==1'b1 && A2==1'b0 && B1_N==1'b1 && X==1'b0));
  cover property (@(A1 or A2 or B1_N or X)
    !$isunknown({A1,A2,B1_N}) && (A1==1'b1 && A2==1'b1 && B1_N==1'b1 && X==1'b1));

  // Simple toggle coverage
  cover property (@(A1) $rose(A1));  cover property (@(A1) $fell(A1));
  cover property (@(A2) $rose(A2));  cover property (@(A2) $fell(A2));
  cover property (@(B1_N) $rose(B1_N)); cover property (@(B1_N) $fell(B1_N));
  cover property (@(X) $rose(X));    cover property (@(X) $fell(X));

endmodule

// Bind into the DUT
bind sky130_fd_sc_ms__a21bo sky130_fd_sc_ms__a21bo_sva sva_i (.A1(A1), .A2(A2), .B1_N(B1_N), .X(X));