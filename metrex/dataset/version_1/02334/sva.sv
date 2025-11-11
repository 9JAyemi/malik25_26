// SVA for SUB_1 and ADD. Bind these checkers to the DUTs.

module SUB_1_sva #(parameter N = 32)(
  input  [N-1:0] A, B,
  input  [N:0]   D,
  input          CO   // internal from SUB_1
);
  localparam [N-1:0] MAX = {N{1'b1}};

  // Combinational correctness and X-propagation checks
  always_comb begin
    if (!$isunknown({A,B})) begin
      // Functional: D = {borrow, A-B}, borrow = (A<B)
      assert ({(A < B), (A - B)} == D)
        else $error("SUB_1: D mismatch A=%0h B=%0h D=%0h", A, B, D);

      // Structural: MSB ties to ~CO from internal adder
      assert (D[N] == ~CO)
        else $error("SUB_1: D[N] != ~CO A=%0h B=%0h D=%0h CO=%0b", A, B, D, CO);

      // Two's complement add equivalence: {~borrow, diff} == A + ~B + 1
      assert ({~D[N], D[N-1:0]} == ({1'b0, A} + {1'b0, ~B} + 1'b1))
        else $error("SUB_1: add-eq mismatch A=%0h B=%0h D=%0h", A, B, D);

      // No X on outputs when inputs are known
      assert (!$isunknown(D))
        else $error("SUB_1: X/Z on D A=%0h B=%0h D=%0h", A, B, D);
    end

    // Coverage: key corner and partition cases
    cover (A == B && D[N] == 1'b0 && D[N-1:0] == {N{1'b0}}); // zero result, no borrow
    cover (A <  B && D[N] == 1'b1);                         // borrow case
    cover (A >  B && D[N] == 1'b0);                         // no borrow case
    cover (A == {N{1'b0}} && B == {N{1'b0}});               // 0 - 0
    cover (A == {N{1'b0}} && B == {{(N-1){1'b0}},1'b1});    // 0 - 1
    cover (A == MAX && B == {N{1'b0}});                     // max - 0
    cover (A == {N{1'b0}} && B == MAX);                     // 0 - max
  end
endmodule

bind SUB_1 SUB_1_sva #(.N(N)) sub_1_sva_i ( .A(A), .B(B), .D(D), .CO(CO) );

module ADD_sva #(parameter N = 32)(
  input  [N-1:0] A, B,
  input          CI,
  input  [N-1:0] S,
  input          CO
);
  // Combinational correctness and X-propagation checks
  always_comb begin
    if (!$isunknown({A,B,CI})) begin
      // Functional: {CO,S} = A + B + CI
      assert ({CO, S} == ({1'b0, A} + {1'b0, B} + CI))
        else $error("ADD: sum mismatch A=%0h B=%0h CI=%0b S=%0h CO=%0b", A, B, CI, S, CO);

      // No X on outputs when inputs are known
      assert (!$isunknown({S,CO}))
        else $error("ADD: X/Z on outputs A=%0h B=%0h CI=%0b S=%0h CO=%0b", A, B, CI, S, CO);
    end

    // Coverage: carry/no-carry, CI polarity, extremes
    cover (CI == 1'b0);
    cover (CI == 1'b1);
    cover (CO == 1'b0);
    cover (CO == 1'b1);
    cover (S == {N{1'b0}}); // zero sum
    cover (&S);             // all ones
  end
endmodule

bind ADD ADD_sva #(.N(N)) add_sva_i ( .A(A), .B(B), .CI(CI), .S(S), .CO(CO) );