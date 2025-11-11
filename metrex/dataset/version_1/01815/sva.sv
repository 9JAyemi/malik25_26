// SVA for mag_comp: functional correctness, mutual exclusivity, and basic coverage.
// Bind this module to mag_comp; uses only I/O to stay implementation-agnostic.

module mag_comp_sva #(parameter int n = 8)
(
  input  logic [n-1:0] A,
  input  logic [n-1:0] B,
  input  logic         A_greater_than_B,
  input  logic         A_equal_to_B,
  input  logic         A_less_than_B
);

  // Core checks (combinational, guarded against X/Z on inputs)
  always_comb begin
    bit inputs_known  = !$isunknown({A,B});
    if (inputs_known) begin
      assert (!$isunknown({A_greater_than_B, A_equal_to_B, A_less_than_B}))
        else $error("mag_comp: outputs contain X/Z for known inputs A=%0h B=%0h", A, B);

      assert ($onehot({A_greater_than_B, A_equal_to_B, A_less_than_B}))
        else $error("mag_comp: outputs not one-hot for A=%0h B=%0h", A, B);

      assert (A_equal_to_B     == (A == B))
        else $error("mag_comp: A_equal_to_B mismatch A=%0h B=%0h", A, B);

      assert (A_greater_than_B == (A > B))
        else $error("mag_comp: A_greater_than_B mismatch A=%0h B=%0h", A, B);

      assert (A_less_than_B    == (A < B))
        else $error("mag_comp: A_less_than_B mismatch A=%0h B=%0h", A, B);
    end

    // Even with X/Z on inputs, contradictory outputs are illegal
    assert (!(A_greater_than_B && A_less_than_B))
      else $error("mag_comp: > and < both asserted (contradiction)");
  end

  // Lightweight functional coverage
  localparam logic [n-1:0] MAX = {n{1'b1}};
  always_comb begin
    cover (A == B);
    cover (A > B);
    cover (A < B);
    cover (A == '0 && B == '0);
    cover (A == MAX && B == '0);
    cover (A == '0 && B == MAX);
    cover ($onehot(A ^ B));                // single-bit difference somewhere
    cover ((A ^ B) == (1 << (n-1)));       // MSB differs only
  end

endmodule

bind mag_comp mag_comp_sva #(.n(n)) mag_comp_sva_i (.*);