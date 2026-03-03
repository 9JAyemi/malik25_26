// SVA for comparator_block: concise, bindable, and comprehensive

module comparator_block_sva #(
  parameter int N = 8
)(
  input  logic [N-1:0] a,
  input  logic [N-1:0] b,
  input  logic         gt,
  input  logic         lt,
  input  logic         eq
);

  // Parameter sanity
  initial assert (N >= 1)
    else $error("comparator_block_sva: N must be >= 1");

  // Combinational checks guarded against X/Z on inputs
  always_comb begin
    if (!$isunknown({a,b})) begin
      // No X/Z on outputs when inputs are known
      assert (!$isunknown({gt,lt,eq}))
        else $error("Outputs contain X/Z with known inputs");

      // Functional correctness
      assert (eq == (a == b))
        else $error("eq mismatch: expected (a==b)");
      assert (gt == |(a & ~b))
        else $error("gt mismatch: expected |(a & ~b)");
      assert (lt == |(~a & b))
        else $error("lt mismatch: expected |(~a & b)");

      // Relationship among outputs: eq iff neither gt nor lt
      assert (eq == ~(gt | lt))
        else $error("eq must be the inverse of (gt|lt)");

      // Key scenario coverage
      cover (a == b               &&  eq && !gt && !lt); // equality
      cover ((a & ~b) != '0       &&  gt && !lt && !eq); // gt only
      cover ((~a & b) != '0       &&  lt && !gt && !eq); // lt only
      cover ((a & ~b) != '0 && (~a & b) != '0 && gt && lt && !eq); // both gt and lt

      // Boundary/value coverage
      cover (a == '0              && b == '0              && eq);
      cover (a == {N{1'b1}}       && b == '0              && gt && !lt);
      cover (a == '0              && b == {N{1'b1}}       && lt && !gt);
    end
  end

endmodule

// Bind to all instances of comparator_block; inherit the DUT parameter n
bind comparator_block comparator_block_sva #(.N(n)) u_comparator_block_sva (.*);