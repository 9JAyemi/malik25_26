// SVA checker for adder_8bit
// Bind into the DUT as shown at the bottom.

module adder_8bit_sva
  #(parameter WIDTH = 8)
(
  input  logic [WIDTH-1:0] A,
  input  logic [WIDTH-1:0] B,
  input  logic [WIDTH-1:0] S,
  input  logic             C_out,
  // Internal carry chain from DUT (wire [7:0] c)
  input  logic [WIDTH-1:0] c
);

  logic [WIDTH:0] sum_ref;
  logic [WIDTH:0] carry;
  integer i;

  always_comb begin
    sum_ref = A + B;

    // Canonical ripple-carry chain from LSB upward (spec)
    carry[0] = 1'b0;
    for (i = 0; i < WIDTH; i++) begin
      carry[i+1] = (A[i] & B[i]) | ((A[i] ^ B[i]) & carry[i]);
    end

    // Functional equivalence: strongest single check
    assert ({C_out, S} === sum_ref)
      else $error("adder_8bit SVA: {C_out,S} != A+B (A=%0h B=%0h S=%0h C_out=%0b ref=%0h)",
                  A, B, S, C_out, sum_ref);

    // Bit-slice full-adder equations
    for (i = 0; i < WIDTH; i++) begin
      assert (S[i] === (A[i] ^ B[i] ^ carry[i]))
        else $error("adder_8bit SVA: S[%0d] wrong (A=%0b B=%0b cin=%0b S=%0b)",
                    i, A[i], B[i], carry[i], S[i]);
    end
    assert (C_out === carry[WIDTH])
      else $error("adder_8bit SVA: C_out wrong (exp=%0b got=%0b)", carry[WIDTH], C_out);

    // Internal carry net consistency (expects c[i] == carry-out of bit i)
    for (i = 0; i < WIDTH; i++) begin
      assert (c[i] === carry[i+1])
        else $error("adder_8bit SVA: c[%0d] wrong (exp=%0b got=%0b)", i, carry[i+1], c[i]);
    end

    // Sanity: outputs must never be X/Z
    assert (!$isunknown({S, C_out}))
      else $error("adder_8bit SVA: X/Z on outputs S=%b C_out=%b", S, C_out);

    // Lightweight coverage (gated to input changes)
    if ($changed({A,B})) begin
      // Corner/summary cases
      cover (C_out == 0);
      cover (C_out == 1);
      cover (A == '0 && B == '0);
      cover (A == '0 && B == '1);
      cover (A == {WIDTH{1'b1}} && B == '0);
      cover (A == {WIDTH{1'b1}} && B == {WIDTH{1'b1}});
      cover (S == '0);
      cover (S == {WIDTH{1'b1}});

      // Per-bit generate/propagate/kill exposure
      for (i = 0; i < WIDTH; i++) begin
        cover (A[i] & B[i]);          // generate
        cover (A[i] ^ B[i]);          // propagate
        cover (~A[i] & ~B[i]);        // kill
      end

      // Output edge coverage
      cover ($changed(C_out) && C_out);   // 0->1
      cover ($changed(C_out) && !C_out);  // 1->0
    end
  end
endmodule

// Bind into the DUT (place in a testbench or a separate bind file):
// bind adder_8bit adder_8bit_sva #(.WIDTH(8)) (.A(A), .B(B), .S(S), .C_out(C_out), .c(c));