// SVA for mux_4to1
// Concise, high-quality checks and coverage; bind-ready.

module mux_4to1_sva (
  input logic A, B, C, D,
  input logic S0, S1,
  input logic Y
);

  // Functional correctness for known selects (combinational, zero-delay)
  property p_func_known_sel;
    @(A or B or C or D or S0 or S1)
      !$isunknown({S1,S0}) |-> ##0 ( Y === (S1 ? (S0 ? D : C) : (S0 ? B : A)) );
  endproperty
  assert property (p_func_known_sel);

  // Disallow X/Z on selects (avoids latch-through on unknown selects)
  assert property (@(S0 or S1) !$isunknown({S1,S0}));

  // Y changes only due to select change or the currently selected input
  property p_change_cause;
    @(A or B or C or D or S0 or S1 or Y)
      $changed(Y) |-> (
        $changed({S1,S0}) ||
        (({S1,S0}==2'b00) && $changed(A)) ||
        (({S1,S0}==2'b01) && $changed(B)) ||
        (({S1,S0}==2'b10) && $changed(C)) ||
        (({S1,S0}==2'b11) && $changed(D))
      );
  endproperty
  assert property (p_change_cause);

  // Functional coverage: each select path exercised, output matches source
  cover property (@(A or B or C or D or S0 or S1) ({S1,S0}==2'b00) ##0 (Y===A));
  cover property (@(A or B or C or D or S0 or S1) ({S1,S0}==2'b01) ##0 (Y===B));
  cover property (@(A or B or C or D or S0 or S1) ({S1,S0}==2'b10) ##0 (Y===C));
  cover property (@(A or B or C or D or S0 or S1) ({S1,S0}==2'b11) ##0 (Y===D));

  // Coverage: selected input toggles propagate to Y
  cover property (@(A) ({S1,S0}==2'b00 && $rose(A)) ##0 (Y==1));
  cover property (@(A) ({S1,S0}==2'b00 && $fell(A)) ##0 (Y==0));
  cover property (@(B) ({S1,S0}==2'b01 && $rose(B)) ##0 (Y==1));
  cover property (@(B) ({S1,S0}==2'b01 && $fell(B)) ##0 (Y==0));
  cover property (@(C) ({S1,S0}==2'b10 && $rose(C)) ##0 (Y==1));
  cover property (@(C) ({S1,S0}==2'b10 && $fell(C)) ##0 (Y==0));
  cover property (@(D) ({S1,S0}==2'b11 && $rose(D)) ##0 (Y==1));
  cover property (@(D) ({S1,S0}==2'b11 && $fell(D)) ##0 (Y==0));

  // Coverage: Y changes caused by select vs. by selected data
  cover property (@(A or B or C or D or S0 or S1 or Y) $changed(Y) && $changed({S1,S0}));
  cover property (@(A or B or C or D or S0 or S1 or Y)
                   $changed(Y) && !$changed({S1,S0}) &&
                   ((({S1,S0}==2'b00) && $changed(A)) ||
                    (({S1,S0}==2'b01) && $changed(B)) ||
                    (({S1,S0}==2'b10) && $changed(C)) ||
                    (({S1,S0}==2'b11) && $changed(D))));
endmodule

bind mux_4to1 mux_4to1_sva i_mux_4to1_sva (.*);