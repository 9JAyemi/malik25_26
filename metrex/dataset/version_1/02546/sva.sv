// SVA for priority_mux
// Provide a sampling clock from your TB when binding.
module priority_mux_sva (
  input logic              clk,
  input logic [3:0]        A, B, C, D,
  input logic [1:0]        S,
  input logic              Y, Z
);

  default clocking cb @(posedge clk); endclocking

  // Helpers
  let a_any = |A;
  let b_any = |B;
  let c_any = |C;
  let d_any = |D;
  let known_inputs = !$isunknown({A,B,C,D,S});

  // Outputs never unknown when inputs are known
  assert property (known_inputs |-> !$isunknown({Y,Z}));

  // Output encoding is 00, 01, or 10 only
  assert property ($onehot0({Y,Z}));

  // Functional mapping by select S
  assert property (known_inputs && S==2'b00 |-> (Y == a_any) && (Z == (!a_any && b_any)));
  assert property (known_inputs && S==2'b01 |-> (Z == b_any) && (Y == (!b_any && a_any)));
  assert property (known_inputs && S==2'b10 |-> (Y == (!c_any && a_any)) && (Z == (!c_any && !a_any && b_any)));
  assert property (known_inputs && S==2'b11 |-> (Y == (!d_any && a_any)) && (Z == (!d_any && !a_any && b_any)));

  // If neither A nor B asserted, outputs must be 0 regardless of S
  assert property (known_inputs && !a_any && !b_any |-> !Y && !Z);

  // Coverage: exercise key behaviors and priorities
  cover property (known_inputs && S==2'b00 && a_any &&  Y && !Z);
  cover property (known_inputs && S==2'b00 && !a_any && b_any && !Y &&  Z);

  cover property (known_inputs && S==2'b01 && b_any && !Y &&  Z);
  cover property (known_inputs && S==2'b01 && !b_any && a_any &&  Y && !Z);

  cover property (known_inputs && S==2'b10 &&  c_any && !Y && !Z); // C overshadows
  cover property (known_inputs && S==2'b10 && !c_any &&  a_any &&  Y && !Z);
  cover property (known_inputs && S==2'b10 && !c_any && !a_any && b_any && !Y &&  Z);

  cover property (known_inputs && S==2'b11 &&  d_any && !Y && !Z); // D overshadows
  cover property (known_inputs && S==2'b11 && !d_any &&  a_any &&  Y && !Z);
  cover property (known_inputs && S==2'b11 && !d_any && !a_any && b_any && !Y &&  Z);

  cover property (known_inputs && !a_any && !b_any && !c_any && !d_any && !Y && !Z);

endmodule

// Example bind (connect clk from your TB/environment)
// bind priority_mux priority_mux_sva sva ( .clk(clk), .A(A), .B(B), .C(C), .D(D), .S(S), .Y(Y), .Z(Z) );