// SVA for pipelined_ripple_carry_adder_4bit
// Bind this checker to the DUT

module prca4_sva;
  // Bound into DUT scope; can see internals
  default clocking cb @(posedge clk); endclocking

  // Helper
  function automatic [4:0] add5(input [3:0] a, input [3:0] b, input cin);
    add5 = a + b + cin;
  endfunction

  // 1) Stage-1 capture correctness (A/B/Cin -> A_reg/B_reg/Cin_reg one cycle later)
  assert property ( !$isunknown(A)  |-> ##1 (A_reg  == A)  );
  assert property ( !$isunknown(B)  |-> ##1 (B_reg  == B)  );
  assert property ( !$isunknown(Cin)|-> ##1 (Cin_reg== Cin));

  // 2) Top-level functional correctness with 1-cycle latency
  assert property ( !$isunknown({A,B,Cin}) |-> ##1 ({Cout,Sum} == add5(A,B,Cin)) );

  // 3) Internal ripple-carry chain correctness (computed from registered operands)
  assert property (
    !$isunknown({A_reg,B_reg,Cin_reg}) |->
      ##1 (
        {Cout_reg1, Sum[0]} == (A_reg[0] + B_reg[0] + Cin_reg)     &&
        {Cout_reg2, Sum[1]} == (A_reg[1] + B_reg[1] + Cout_reg1)   &&
        {Cout_reg3, Sum[2]} == (A_reg[2] + B_reg[2] + Cout_reg2)   &&
        {Cout     , Sum[3]} == (A_reg[3] + B_reg[3] + Cout_reg3)
      )
  );

  // 4) No-X on outputs one cycle after valid inputs
  assert property ( !$isunknown({A,B,Cin}) |-> ##1 !$isunknown({Sum,Cout}) );

  // 5) Outputs only update on clock edges (no multi-cycle combinational glitch visible at sample points)
  // If they change, they must change at a clock sample
  assert property ( $changed({Sum,Cout}) |-> $rose(clk) );

  // Coverage
  // Basic no-carry and full-carry cases
  cover property ( (A==4'h0 && B==4'h0 && Cin==1'b0) ##1 ({Cout,Sum}==5'h00) );
  cover property ( (A==4'hF && B==4'h0 && Cin==1'b1) ##1 ({Cout,Sum}==5'h10) );

  // Cover carry-out generation and no-carry
  cover property ( ##1 (add5(A,B,Cin)[4]==1'b1) );
  cover property ( ##1 (add5(A,B,Cin)[4]==1'b0) );

  // Cover each internal carry being 1 at least once
  cover property ( ##1 Cout_reg1 );
  cover property ( ##1 Cout_reg2 );
  cover property ( ##1 Cout_reg3 );

  // Sum bit toggles (any bit changes)
  cover property ( $changed(Sum) );

  // Carry out toggles
  cover property ( Cout && !$past(Cout) );
  cover property ( !Cout && $past(Cout) );

endmodule

bind pipelined_ripple_carry_adder_4bit prca4_sva prca4_sva_i();