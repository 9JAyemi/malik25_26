// SVA for sky130_fd_sc_ms__a31o: X = (A1 & A2 & A3) | B1
module sky130_fd_sc_ms__a31o_sva (
  input logic X,
  input logic A1, A2, A3, B1,
  input logic and0_out, or0_out_X
);
  // Combinational functional and structural checks
  always_comb begin
    assert (#0 X === ((A1 & A2 & A3) | B1))
      else $error("a31o func: X != (A1&A2&A3)|B1 A=%b%b%b B1=%b X=%b", A1,A2,A3,B1,X);

    assert (#0 and0_out  === (A1 & A2 & A3))
      else $error("and0_out mismatch");
    assert (#0 or0_out_X === (and0_out | B1))
      else $error("or0_out_X mismatch");
    assert (#0 X === or0_out_X)
      else $error("buf path mismatch");

    if (!$isunknown({A1,A2,A3,B1})) begin
      assert (!$isunknown(X)) else $error("X is X/Z while inputs are known");
    end
  end

  // Eventing for concurrent SVA and coverage
  default clocking cb @(
    posedge A1 or negedge A1 or
    posedge A2 or negedge A2 or
    posedge A3 or negedge A3 or
    posedge B1 or negedge B1 or
    posedge X  or negedge X
  ); endclocking

  // Truth table holds whenever inputs are known
  property p_truth; !$isunknown({A1,A2,A3,B1}) |-> (X === ((A1 & A2 & A3) | B1)); endproperty
  assert property (p_truth);

  // Dominance/special-case checks
  assert property ( B1 && !$isunknown(B1) |-> X == 1'b1);
  assert property (!B1 && !$isunknown(B1) |-> X == (A1 & A2 & A3));

  // Key functional coverage
  cover property (!B1 && A1 && A2 && A3 && X);     // AND path drives 1
  cover property ( B1 && X);                       // OR path drives 1
  cover property (!B1 && !(A1 & A2 & A3) && !X);   // drives 0
  cover property ($rose(X));
  cover property ($fell(X));

  // Full truth-table coverage (inputs with correct X)
  cover property ({A1,A2,A3,B1} == 4'b0000 && X==1'b0);
  cover property ({A1,A2,A3,B1} == 4'b0001 && X==1'b1);
  cover property ({A1,A2,A3,B1} == 4'b0010 && X==1'b0);
  cover property ({A1,A2,A3,B1} == 4'b0011 && X==1'b1);
  cover property ({A1,A2,A3,B1} == 4'b0100 && X==1'b0);
  cover property ({A1,A2,A3,B1} == 4'b0101 && X==1'b1);
  cover property ({A1,A2,A3,B1} == 4'b0110 && X==1'b0);
  cover property ({A1,A2,A3,B1} == 4'b0111 && X==1'b1);
  cover property ({A1,A2,A3,B1} == 4'b1000 && X==1'b0);
  cover property ({A1,A2,A3,B1} == 4'b1001 && X==1'b1);
  cover property ({A1,A2,A3,B1} == 4'b1010 && X==1'b0);
  cover property ({A1,A2,A3,B1} == 4'b1011 && X==1'b1);
  cover property ({A1,A2,A3,B1} == 4'b1100 && X==1'b0);
  cover property ({A1,A2,A3,B1} == 4'b1101 && X==1'b1);
  cover property ({A1,A2,A3,B1} == 4'b1110 && X==1'b1);
  cover property ({A1,A2,A3,B1} == 4'b1111 && X==1'b1);
endmodule

bind sky130_fd_sc_ms__a31o sky130_fd_sc_ms__a31o_sva
(
  .X(X), .A1(A1), .A2(A2), .A3(A3), .B1(B1),
  .and0_out(and0_out), .or0_out_X(or0_out_X)
);