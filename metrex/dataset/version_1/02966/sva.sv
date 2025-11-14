// SVA for comb_logic: q must always equal (a & b), with concise checks and coverage.
module comb_logic_sva (
  input logic a,
  input logic b,
  input logic q
);

  // Functional equivalence (sampled after updates using ##0 from preponed sampling)
  property p_and_func;
    @(posedge a or negedge a or posedge b or negedge b or posedge q or negedge q)
      1'b1 |-> ##0 (q === (a & b));
  endproperty
  assert property (p_and_func)
    else $error("AND mismatch: a=%b b=%b q=%b", a,b,q);

  // No spurious q changes (q only changes when a or b changes)
  property p_q_changes_only_with_inputs;
    @(posedge q or negedge q) 1'b1 |-> ##0 ($changed(a) || $changed(b));
  endproperty
  assert property (p_q_changes_only_with_inputs)
    else $error("q changed without a/b changing: a=%b b=%b q=%b", a,b,q);

  // Truth-table coverage (all 4 input combos, sampled post-update)
  cover property (@(posedge a or negedge a or posedge b or negedge b or posedge q or negedge q) ##0 (a==0 && b==0 && q==0));
  cover property (@(same) ##0 (a==0 && b==1 && q==0));
  cover property (@(same) ##0 (a==1 && b==0 && q==0));
  cover property (@(same) ##0 (a==1 && b==1 && q==1));

  // q toggle coverage
  cover property (@(posedge q));
  cover property (@(negedge q));

endmodule

// Bind into the DUT
bind comb_logic comb_logic_sva u_comb_logic_sva (.a(a), .b(b), .q(q));