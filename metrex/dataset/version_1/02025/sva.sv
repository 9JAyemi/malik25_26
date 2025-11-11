// SVA for sky130_fd_sc_ls__o311a
// Function: X = (A1 | A2 | A3) & B1 & C1

module sky130_fd_sc_ls__o311a_sva (
  input logic X,
  input logic A1,
  input logic A2,
  input logic A3,
  input logic B1,
  input logic C1
);

  // Functional equivalence when inputs are known; allow delta to settle
  property p_func_equiv_known;
    @(*) (!$isunknown({A1,A2,A3,B1,C1})) |-> ##0 (X == ((A1|A2|A3) & B1 & C1));
  endproperty
  assert property (p_func_equiv_known)
    else $error("o311a: functional mismatch with known inputs");

  // Output must be known when inputs are known
  property p_no_x_when_inputs_known;
    @(*) (!$isunknown({A1,A2,A3,B1,C1})) |-> ##0 (!$isunknown(X));
  endproperty
  assert property (p_no_x_when_inputs_known)
    else $error("o311a: X is X/Z with known inputs");

  // Strong one-way implications that must always hold (with X/Z awareness)
  property p_force_zero_B1_0;
    @(*) (B1===1'b0) |-> ##0 (X===1'b0);
  endproperty
  assert property (p_force_zero_B1_0)
    else $error("o311a: B1=0 should force X=0");

  property p_force_zero_C1_0;
    @(*) (C1===1'b0) |-> ##0 (X===1'b0);
  endproperty
  assert property (p_force_zero_C1_0)
    else $error("o311a: C1=0 should force X=0");

  property p_force_zero_As_all0;
    @(*) (A1===1'b0 && A2===1'b0 && A3===1'b0) |-> ##0 (X===1'b0);
  endproperty
  assert property (p_force_zero_As_all0)
    else $error("o311a: A1=A2=A3=0 should force X=0");

  property p_true_case_when_gate_on;
    @(*) (B1===1'b1 && C1===1'b1 && (A1===1'b1 || A2===1'b1 || A3===1'b1)) |-> ##0 (X===1'b1);
  endproperty
  assert property (p_true_case_when_gate_on)
    else $error("o311a: gate on and some A=1 should make X=1");

  // Output 1 implies necessary input conditions
  property p_X1_implies_inputs;
    @(*) (X===1'b1) |-> (B1===1'b1 && C1===1'b1 && (A1===1'b1 || A2===1'b1 || A3===1'b1));
  endproperty
  assert property (p_X1_implies_inputs)
    else $error("o311a: X=1 implies B1=C1=1 and some A=1");

  // Coverage: exercise key functional corners and per-input control
  cover property (@(*) ##0 (B1 && C1 && (A1 || A2 || A3) && X));               // X=1 case
  cover property (@(*) ##0 (!B1 && !X));                                       // B1 gate off
  cover property (@(*) ##0 (!C1 && !X));                                       // C1 gate off
  cover property (@(*) ##0 (B1 && C1 && !A1 && !A2 && !A3 && !X));             // all A=0, gates on -> X=0
  cover property (@(*) ##0 (B1 && C1 &&  A1 && !A2 && !A3 && X));              // A1 alone drives X
  cover property (@(*) ##0 (B1 && C1 && !A1 &&  A2 && !A3 && X));              // A2 alone drives X
  cover property (@(*) ##0 (B1 && C1 && !A1 && !A2 &&  A3 && X));              // A3 alone drives X

endmodule

// Bind into the DUT
bind sky130_fd_sc_ls__o311a sky130_fd_sc_ls__o311a_sva o311a_sva_i (.*);