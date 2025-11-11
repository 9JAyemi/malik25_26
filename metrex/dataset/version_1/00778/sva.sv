// SVA for comb_circuit
module comb_circuit_sva (
  input logic a, b,
  input logic out1, out2
);

  // Inputs-known => outputs-known
  assert property ( (! $isunknown({a,b})) |-> ##0 (! $isunknown({out1,out2})) );

  // Functional correctness (sample after updates)
  assert property (@(posedge a or negedge a or posedge b or negedge b)
                   1'b1 |-> ##0 (out1 === (a ? ~b : b)));
  assert property (@(posedge a or negedge a or posedge b or negedge b)
                   1'b1 |-> ##0 (out2 === (a ? b : ~b)));
  assert property (@(posedge a or negedge a or posedge b or negedge b)
                   1'b1 |-> ##0 (out1 === ~out2));

  // No unexpected output edges (every out edge is caused by an input edge)
  assert property (@(posedge out1 or negedge out1) $changed(a) or $changed(b));
  assert property (@(posedge out2 or negedge out2) $changed(a) or $changed(b));

  // Functional coverage: all input/output combinations
  cover property (@(posedge a or negedge a or posedge b or negedge b)
                  ##0 (!a && !b && out1===1'b0 && out2===1'b1));
  cover property (@(posedge a or negedge a or posedge b or negedge b)
                  ##0 (!a &&  b && out1===1'b1 && out2===1'b0));
  cover property (@(posedge a or negedge a or posedge b or negedge b)
                  ##0 ( a && !b && out1===1'b1 && out2===1'b0));
  cover property (@(posedge a or negedge a or posedge b or negedge b)
                  ##0 ( a &&  b && out1===1'b0 && out2===1'b1));

  // Dynamic coverage: a-edge inverts both outputs when b is stable
  cover property (@(posedge a or negedge a) $stable(b) ##0 ($changed(out1) && $changed(out2)));
  // Dynamic coverage: b-edge propagates correctly in both a states
  cover property (@(posedge b or negedge b) (a==1'b0) ##0 (out1===b && out2===~b));
  cover property (@(posedge b or negedge b) (a==1'b1) ##0 (out1===~b && out2===b));

endmodule

bind comb_circuit comb_circuit_sva comb_circuit_sva_i (.*);