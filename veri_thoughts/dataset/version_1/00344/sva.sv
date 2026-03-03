// SVA checker for barrel_shifter
module barrel_shifter_sva (
  input  logic [3:0] A,
  input  logic [3:0] B,
  input  logic [1:0] S,
  input  logic [3:0] Y
);

  // Golden model
  function automatic logic [3:0] rot4 (input logic [3:0] a, input logic [1:0] s);
    unique case (s)
      2'b00: rot4 = a;
      2'b01: rot4 = {a[2:0], a[3]};
      2'b10: rot4 = {a[0], a[3:1]};
      2'b11: rot4 = {a[1:0], a[3:2]};
      default: rot4 = 'x;
    endcase
  endfunction

  // Functional equivalence (inputs known => output must match model)
  a_func_eq: assert property (@(A or S or Y)
                              (!$isunknown({A,S})) |-> (Y == rot4(A,S)))
    else $error("barrel_shifter: Y != rotate(A,S)");

  // Output must be known if inputs are known
  a_known:   assert property (@(A or S or Y)
                              (!$isunknown({A,S})) |-> !$isunknown(Y))
    else $error("barrel_shifter: Y has X/Z with known inputs");

  // B is functionally irrelevant (changing B alone must not change Y)
  a_b_irrel: assert property (@(A or S or B or Y)
                              ($changed(B) && $stable(A) && $stable(S)) |-> $stable(Y))
    else $error("barrel_shifter: Y changed due to B");

  // Rotation preserves popcount (with known inputs)
  a_popcnt:  assert property (@(A or S or Y)
                              (!$isunknown({A,S})) |-> ($countones(Y) == $countones(A)))
    else $error("barrel_shifter: popcount not preserved");

  // Basic functional coverage of all select values
  c_s00: cover property (@(A or S) S == 2'b00);
  c_s01: cover property (@(A or S) S == 2'b01);
  c_s10: cover property (@(A or S) S == 2'b10);
  c_s11: cover property (@(A or S) S == 2'b11);

  // Cover that B toggles while A,S stable (to exercise a_b_irrel)
  c_b_only_change: cover property (@(A or S or B)
                                   $changed(B) && $stable(A) && $stable(S));

  // Cover wrap-around activity for 1-bit left/right rotates
  c_wrap_l1: cover property (@(A or S) (S == 2'b01) && (A[3] != A[0]));
  c_wrap_r1: cover property (@(A or S) (S == 2'b10) && (A[0] != A[3]));

endmodule

// Bind into the DUT
bind barrel_shifter barrel_shifter_sva u_barrel_shifter_sva (.A(A), .B(B), .S(S), .Y(Y));