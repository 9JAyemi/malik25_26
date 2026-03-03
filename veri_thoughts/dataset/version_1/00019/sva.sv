// SVA checker for priority_mux
// Uses immediate assertions/covers (no clock required). Bind into DUT.

module priority_mux_sva (
  input [3:0] A, B, C, D,
  input [1:0] S,
  input       Y, Z
);
  // Treat 4-bit inputs as booleans (any bit set)
  wire a = |A;
  wire b = |B;
  wire c = |C;
  wire d = |D;

  // Expected behavior per RTL
  wire expY =
      (S==2'b00 &&  a               ) ||
      (S==2'b01 && !b && a          ) ||
      (S==2'b10 && !c && a          ) ||
      (S==2'b11 && !d && a          );

  wire expZ =
      (S==2'b00 && !a && b          ) ||
      (S==2'b01 &&  b               ) ||
      (S==2'b10 && !c && !a && b    ) ||
      (S==2'b11 && !d && !a && b    );

  // Basic sanity
  always @* begin
    assert (!$isunknown({S,a,b,c,d})) else $error("X/Z on inputs");
    assert (!$isunknown({Y,Z}))       else $error("X/Z on outputs");
    assert (!(Y & Z))                 else $error("Illegal Y&Z both 1");
  end

  // Functional correctness
  always @* begin
    assert (Y == expY) else $error("Y mismatch");
    assert (Z == expZ) else $error("Z mismatch");
  end

  // Functional coverage (exercise all priority/branch outcomes)
  always @* begin
    // S=00: A> B> C/D/none (all yield 00 except A/B)
    cover (S==2'b00 &&  a);
    cover (S==2'b00 && !a &&  b);
    cover (S==2'b00 && !a && !b &&  c);
    cover (S==2'b00 && !a && !b && !c &&  d);
    cover (S==2'b00 && !a && !b && !c && !d);

    // S=01: B> A> C/D/none
    cover (S==2'b01 &&  b);
    cover (S==2'b01 && !b &&  a);
    cover (S==2'b01 && !b && !a &&  c);
    cover (S==2'b01 && !b && !a &&  d);
    cover (S==2'b01 && !b && !a && !c && !d);

    // S=10: C> A> B> D/none
    cover (S==2'b10 &&  c);
    cover (S==2'b10 && !c &&  a);
    cover (S==2'b10 && !c && !a &&  b);
    cover (S==2'b10 && !c && !a && !b &&  d);
    cover (S==2'b10 && !c && !a && !b && !d);

    // S=11: D> A> B> C/none
    cover (S==2'b11 &&  d);
    cover (S==2'b11 && !d &&  a);
    cover (S==2'b11 && !d && !a &&  b);
    cover (S==2'b11 && !d && !a && !b &&  c);
    cover (S==2'b11 && !d && !a && !b && !c);
  end
endmodule

// Bind into the DUT
bind priority_mux priority_mux_sva sva_i (.*);