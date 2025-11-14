// SVA for MUX4X1 – concise, full functional checks and coverage
module MUX4X1_sva (input logic A,B,C,D,S0,S1,Y);

  // Functional equivalence (for known selects)
  property p_mux_func;
    @(A or B or C or D or S0 or S1)
      !$isunknown({S1,S0}) |-> ##0 (Y === (S1 ? (S0 ? D : C) : (S0 ? B : A)));
  endproperty
  assert property (p_mux_func);

  // Y must be known when all inputs/selects are known
  property p_y_known_if_inputs_known;
    @(A or B or C or D or S0 or S1)
      !$isunknown({A,B,C,D,S1,S0}) |-> ##0 !$isunknown(Y);
  endproperty
  assert property (p_y_known_if_inputs_known);

  // No spurious Y change: if selects stable and known, Y can change only due to selected input
  property p_y_change_has_cause;
    @(A or B or C or D or S0 or S1)
      $changed(Y) && !$isunknown({S1,S0}) && !$changed({S1,S0}) |->
        ##0 ( ({S1,S0}==2'b00 && $changed(A)) ||
              ({S1,S0}==2'b01 && $changed(B)) ||
              ({S1,S0}==2'b10 && $changed(C)) ||
              ({S1,S0}==2'b11 && $changed(D)) );
  endproperty
  assert property (p_y_change_has_cause);

  // Coverage: each select case observed with correct output
  cover property (@(A or B or C or D or S0 or S1) {S1,S0}==2'b00 ##0 (Y===A));
  cover property (@(A or B or C or D or S0 or S1) {S1,S0}==2'b01 ##0 (Y===B));
  cover property (@(A or B or C or D or S0 or S1) {S1,S0}==2'b10 ##0 (Y===C));
  cover property (@(A or B or C or D or S0 or S1) {S1,S0}==2'b11 ##0 (Y===D));

  // Coverage: data-path toggle seen on Y for each select
  cover property (@(A or B or C or D or S0 or S1) {S1,S0}==2'b00 && $changed(A) ##0 $changed(Y));
  cover property (@(A or B or C or D or S0 or S1) {S1,S0}==2'b01 && $changed(B) ##0 $changed(Y));
  cover property (@(A or B or C or D or S0 or S1) {S1,S0}==2'b10 && $changed(C) ##0 $changed(Y));
  cover property (@(A or B or C or D or S0 or S1) {S1,S0}==2'b11 && $changed(D) ##0 $changed(Y));

endmodule

bind MUX4X1 MUX4X1_sva i_MUX4X1_sva(.A(A),.B(B),.C(C),.D(D),.S0(S0),.S1(S1),.Y(Y));