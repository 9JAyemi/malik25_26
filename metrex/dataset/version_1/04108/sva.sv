// SVA for and_gate
module and_gate_sva (input A1, A2, A3, A4, Y);

  // Sample on any input or output edge
  default clocking cb @(
      posedge A1 or negedge A1 or
      posedge A2 or negedge A2 or
      posedge A3 or negedge A3 or
      posedge A4 or negedge A4 or
      posedge Y  or negedge Y
  ); endclocking

  // Functional equivalence (4-state)
  assert property (Y === (A1 & A2 & A3 & A4))
    else $error("and_gate: Y != A1&A2&A3&A4");

  // Output transitions are legal only when inputs warrant it
  assert property ($rose(Y) |-> ##0 (A1===1 && A2===1 && A3===1 && A4===1))
    else $error("and_gate: Y rose without all inputs high");
  assert property ($fell(Y) |-> ##0 (A1===0 || A2===0 || A3===0 || A4===0))
    else $error("and_gate: Y fell without some input low");

  // Known-propagation: if inputs known, output must be known
  assert property (!$isunknown({A1,A2,A3,A4}) |-> ##0 !$isunknown(Y))
    else $error("and_gate: Y unknown while inputs known");

  // Minimal functional coverage
  cover property (A1 && A2 && A3 && A4 && Y);              // Y=1 case
  cover property (!A1 &&  A2 &&  A3 &&  A4 && !Y);
  cover property ( A1 && !A2 &&  A3 &&  A4 && !Y);
  cover property ( A1 &&  A2 && !A3 &&  A4 && !Y);
  cover property ( A1 &&  A2 &&  A3 && !A4 && !Y);
  cover property ($rose(Y));
  cover property ($fell(Y));

  // Full 16-combo input coverage + Y coverage
  covergroup cg_inputs @(cb);
    cpA1: coverpoint A1;
    cpA2: coverpoint A2;
    cpA3: coverpoint A3;
    cpA4: coverpoint A4;
    x_in: cross cpA1, cpA2, cpA3, cpA4;
    cpY:  coverpoint Y;
  endgroup
  cg_inputs cg = new();

endmodule

bind and_gate and_gate_sva and_gate_sva_i (.*);