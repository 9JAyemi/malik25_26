// SVA checker for comparator. Bind this to the DUT.
// - Ensures outputs match relational ops
// - Ensures one-hot encoding when inputs are known
// - Ensures X/Z on inputs propagate to outputs
// - Covers all outcomes and all A/B value pairs

module comparator_sva (
  input logic [1:0] A,
  input logic [1:0] B,
  input logic       equal,
  input logic       greater_than,
  input logic       less_than
);

  // Combinational immediate assertions and coverage
  always_comb begin
    bit in_known = !$isunknown({A,B});
    if (in_known) begin
      assert (equal        === (A == B))
        else $error("comparator equal mismatch: A=%0d B=%0d eq=%0b", A, B, equal);
      assert (greater_than === (A > B))
        else $error("comparator greater_than mismatch: A=%0d B=%0d gt=%0b", A, B, greater_than);
      assert (less_than    === (A < B))
        else $error("comparator less_than mismatch: A=%0d B=%0d lt=%0b", A, B, less_than);

      assert ($onehot({equal, greater_than, less_than}))
        else $error("comparator outputs not one-hot: eq=%0b gt=%0b lt=%0b", equal, greater_than, less_than);

      // Outcome coverage
      cover (A == B && equal);
      cover (A >  B && greater_than);
      cover (A <  B && less_than);
    end
    else begin
      // Unknown inputs should yield unknown outputs with 4-state operators
      assert ($isunknown({equal, greater_than, less_than}))
        else $error("comparator X/Z on inputs must propagate to outputs");
    end
  end

  // Value-pair coverage for all A/B combinations
  genvar i, j;
  generate
    for (i = 0; i < 4; i++) begin : GA
      for (j = 0; j < 4; j++) begin : GB
        always_comb cover (!$isunknown({A,B}) && A == i[1:0] && B == j[1:0]);
      end
    end
  endgenerate

endmodule

// Bind into the DUT
bind comparator comparator_sva u_comparator_sva (
  .A(A),
  .B(B),
  .equal(equal),
  .greater_than(greater_than),
  .less_than(less_than)
);