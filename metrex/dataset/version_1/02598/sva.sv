// SVA for mux_2to1
module mux_2to1_sva (
  input logic A,
  input logic B,
  input logic SEL,
  input logic Y,
  input logic VPWR,
  input logic VGND,
  input logic not_sel,
  input logic and1_out,
  input logic and2_out
);
  logic power_good;
  assign power_good = (VPWR === 1'b1) && (VGND === 1'b0);

  default disable iff (!power_good);

  // Internal gate correctness
  assert property (@(SEL) ##0 (not_sel == ~SEL));
  assert property (@(A or not_sel) ##0 (and1_out == (A & not_sel)));
  assert property (@(B or SEL)    ##0 (and2_out == (B & SEL)));

  // Output composition and mux function
  assert property (@(and1_out or and2_out) ##0 (Y == (and1_out | and2_out)));
  assert property (@(A or B or SEL)        ##0 (Y == (SEL ? B : A)));

  // Sanity: no X/Z on key nodes when powered
  assert property (@(A or B or SEL) ##0 (!$isunknown({not_sel, and1_out, and2_out, Y})));

  // Sanity: mutually exclusive AND outputs (post-settle)
  assert property (@(A or B or SEL) ##0 (!(and1_out && and2_out)));

  // Truth-table coverage (all 8 input combinations with expected Y)
  cover property (@(A or B or SEL) ##0 (SEL==0 && A==0 && B==0 && Y==0));
  cover property (@(A or B or SEL) ##0 (SEL==0 && A==0 && B==1 && Y==0));
  cover property (@(A or B or SEL) ##0 (SEL==0 && A==1 && B==0 && Y==1));
  cover property (@(A or B or SEL) ##0 (SEL==0 && A==1 && B==1 && Y==1));
  cover property (@(A or B or SEL) ##0 (SEL==1 && A==0 && B==0 && Y==0));
  cover property (@(A or B or SEL) ##0 (SEL==1 && A==0 && B==1 && Y==1));
  cover property (@(A or B or SEL) ##0 (SEL==1 && A==1 && B==0 && Y==0));
  cover property (@(A or B or SEL) ##0 (SEL==1 && A==1 && B==1 && Y==1));

  // Path coverage: select switches and selected input toggles
  cover property (@(posedge SEL)  ##0 (Y==B));
  cover property (@(negedge SEL)  ##0 (Y==A));
  cover property (@(posedge A or negedge A) (SEL==0) ##0 (Y==A));
  cover property (@(posedge B or negedge B) (SEL==1) ##0 (Y==B));
endmodule

// Bind into the DUT to access internal wires
bind mux_2to1 mux_2to1_sva i_mux_2to1_sva (
  .A(A), .B(B), .SEL(SEL), .Y(Y), .VPWR(VPWR), .VGND(VGND),
  .not_sel(not_sel), .and1_out(and1_out), .and2_out(and2_out)
);