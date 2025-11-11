// SVA for bitwise_and. Focused, high-signal-quality checks and coverage.
module bitwise_and_sva #(parameter int WIDTH=8)
(
  input logic [WIDTH-1:0] A,
  input logic [WIDTH-1:0] B,
  input logic [WIDTH-1:0] Z
);

  // Functional equivalence (4-state): Z must be A & B at all times
  assert property (@(A or B or Z) Z === (A & B))
    else $error("bitwise_and: Z != (A & B)");

  // No spurious output change without input change
  assert property (@(A or B or Z) $changed(Z) |-> ($changed(A) || $changed(B)))
    else $error("bitwise_and: Z changed without A/B change");

  // If inputs are 2-state, output must be 2-state
  assert property (@(A or B) (!$isunknown(A) && !$isunknown(B)) |-> !$isunknown(Z))
    else $error("bitwise_and: 2-state inputs produced X/Z on Z");

  // Per-bit causality and truth-table reductions + coverage
  genvar i;
  for (i = 0; i < WIDTH; i++) begin : g_perbit
    // Output bit changes only due to corresponding input bit(s)
    assert property (@(A[i] or B[i] or Z[i]) $changed(Z[i]) |-> ($changed(A[i]) || $changed(B[i])))
      else $error("bitwise_and: Z[%0d] changed without A[%0d]/B[%0d] change", i,i,i);

    // Absorption and identity (strengthen debug localization)
    assert property (@(A[i] or B[i]) (A[i] === 1'b0 || B[i] === 1'b0) |-> Z[i] === 1'b0)
      else $error("bitwise_and: zero absorption violated at bit %0d", i);
    assert property (@(A[i] or B[i]) (A[i] === 1'b1) |-> Z[i] === B[i])
      else $error("bitwise_and: identity A=1 violated at bit %0d", i);
    assert property (@(A[i] or B[i]) (B[i] === 1'b1) |-> Z[i] === A[i])
      else $error("bitwise_and: identity B=1 violated at bit %0d", i);

    // Truth-table coverage (only counts when values are 0/1 and Z is correct)
    cover property (@(A[i] or B[i]) (A[i]===1'b0 && B[i]===1'b0 && Z[i]===1'b0));
    cover property (@(A[i] or B[i]) (A[i]===1'b0 && B[i]===1'b1 && Z[i]===1'b0));
    cover property (@(A[i] or B[i]) (A[i]===1'b1 && B[i]===1'b0 && Z[i]===1'b0));
    cover property (@(A[i] or B[i]) (A[i]===1'b1 && B[i]===1'b1 && Z[i]===1'b1));
  end

  // Bus-level corner coverage
  cover property (@(A or B) A=={WIDTH{1'b0}} && B=={WIDTH{1'b0}} && Z=={WIDTH{1'b0}});
  cover property (@(A or B) A=={WIDTH{1'b1}} && B=={WIDTH{1'b1}} && Z=={WIDTH{1'b1}});
  cover property (@(A or B) A=={WIDTH{1'b1}} && B=={WIDTH{1'b0}} && Z=={WIDTH{1'b0}});
  cover property (@(A or B) A=={WIDTH{1'b0}} && B=={WIDTH{1'b1}} && Z=={WIDTH{1'b0}});
endmodule

// Bind into the DUT
bind bitwise_and bitwise_and_sva #(.WIDTH(8)) u_bitwise_and_sva (.A(A), .B(B), .Z(Z));