// SVA for and4
module and4_sva (
  input logic A, B, C, D,
  input logic X,
  input logic VPWR, VGND
);

  // Sample on any input edge to catch combinational behavior
  default clocking cb @(
    posedge A or negedge A or
    posedge B or negedge B or
    posedge C or negedge C or
    posedge D or negedge D
  ); endclocking

  // Functional correctness (4-state)
  a_func:         assert property (X === (A & B & C & D));

  // 0-dominance on each input
  a_domA:         assert property (!A |-> (X === 1'b0));
  a_domB:         assert property (!B |-> (X === 1'b0));
  a_domC:         assert property (!C |-> (X === 1'b0));
  a_domD:         assert property (!D |-> (X === 1'b0));

  // All ones implies output 1
  a_all1:         assert property ((A && B && C && D) |-> (X === 1'b1));

  // No X on output when inputs are fully resolved
  a_no_x_out:     assert property ((!$isunknown({A,B,C,D})) |-> (!$isunknown(X)));

  // Output changes only when some input changes
  a_hold:         assert property (!$changed({A,B,C,D}) |-> !$changed(X));
  a_no_spurious:  assert property ($changed(X) |-> $changed({A,B,C,D}));

  // Power rails sanity (checked at each sample)
  a_rails:        assert property (1'b1 |-> (VPWR === 1'b1 && VGND === 1'b0));

  // Coverage: all 16 input combinations
  c_0000: cover property (!A && !B && !C && !D);
  c_0001: cover property (!A && !B && !C &&  D);
  c_0010: cover property (!A && !B &&  C && !D);
  c_0011: cover property (!A && !B &&  C &&  D);
  c_0100: cover property (!A &&  B && !C && !D);
  c_0101: cover property (!A &&  B && !C &&  D);
  c_0110: cover property (!A &&  B &&  C && !D);
  c_0111: cover property (!A &&  B &&  C &&  D);
  c_1000: cover property ( A && !B && !C && !D);
  c_1001: cover property ( A && !B && !C &&  D);
  c_1010: cover property ( A && !B &&  C && !D);
  c_1011: cover property ( A && !B &&  C &&  D);
  c_1100: cover property ( A &&  B && !C && !D);
  c_1101: cover property ( A &&  B && !C &&  D);
  c_1110: cover property ( A &&  B &&  C && !D);
  c_1111: cover property ( A &&  B &&  C &&  D);

  // Output transition coverage
  c_x_rise: cover property ($rose(X));
  c_x_fall: cover property ($fell(X));

endmodule

// Bind into DUT
bind and4 and4_sva u_and4_sva(.A(A), .B(B), .C(C), .D(D), .X(X), .VPWR(VPWR), .VGND(VGND));