// SVA checker for logic_expression
// Binds to DUT, recomputes expected X, asserts equivalence, and provides full input coverage.

module logic_expression_sva_chk (
  input logic A, B, C, D, E,
  input logic X
);

  // Minterms from spec (w1..w12)
  logic [11:0] m;
  assign m[0]  = (~A & ~B & ~C &  D & ~E);
  assign m[1]  = (~A & ~B & ~C &  D &  E);
  assign m[2]  = (~A & ~B &  C & ~D &  E);
  assign m[3]  = (~A & ~B &  C &  D &  E);
  assign m[4]  = (~A &  B & ~C & ~D &  E);
  assign m[5]  = (~A &  B & ~C &  D &  E);
  assign m[6]  = (~A &  B &  C & ~D &  E);
  assign m[7]  = ( A & ~B & ~C & ~D &  E);
  assign m[8]  = ( A & ~B & ~C &  D &  E);
  assign m[9]  = ( A & ~B &  C &  D &  E);
  assign m[10] = ( A &  B &  C & ~D &  E);
  assign m[11] = ( A &  B &  C &  D &  E);

  logic expX;
  assign expX = |m;

  function automatic bit inputs_known();
    return !$isunknown({A,B,C,D,E});
  endfunction

  // Combinational assertions (no clock needed)
  always_comb begin
    if (inputs_known()) begin
      assert (!$isunknown(X))
        else $error("X is X/Z with known inputs A=%0b B=%0b C=%0b D=%0b E=%0b", A,B,C,D,E);

      assert (X == expX)
        else $error("X mismatch. A=%0b B=%0b C=%0b D=%0b E=%0b expX=%0b got=%0b", A,B,C,D,E,expX,X);

      // Sanity: minterms are mutually exclusive
      assert ($onehot0(m))
        else $error("Overlapping minterms detected for A=%0b B=%0b C=%0b D=%0b E=%0b (m=%0h)", A,B,C,D,E,m);

      // Key special-case check: when E==0, only one way to get X==1
      if (!E)
        assert (X == (~A & ~B & ~C & D))
          else $error("E=0 gating violated. A=%0b B=%0b C=%0b D=%0b X=%0b", A,B,C,D,X);
    end
  end

  // Functional coverage: all 32 input combinations and their X
  event ev; always @* -> ev;
  covergroup cg_inputs @(ev);
    cp_inputs: coverpoint {A,B,C,D,E} { bins all[] = {[0:31]}; }
    x_by_inputs: cross cp_inputs, X;
  endgroup
  cg_inputs cg = new();

endmodule

bind logic_expression logic_expression_sva_chk sva (.A(A), .B(B), .C(C), .D(D), .E(E), .X(X));