// SVA for bitwise_add_sub
module bitwise_add_sub_sva;

  // Access DUT signals via bind scope
  default clocking cb @(posedge clk); endclocking
  default disable iff (!reset)

  // Short-hands for pipeline-aligned values
  let a1   = $past(a_shifted, 1, !reset);
  let b1   = $past(b_shifted, 1, !reset);
  let ia2  = $past(in_a,      2, !reset);
  let ib2  = $past(in_b,      2, !reset);
  let sel1 = $past(select,    1, !reset);

  let add8 = (a1 + b1) & 8'hFF;
  let sub8 = (a1 - b1) & 8'hFF;
  let op8_stage2 = sel1 ? ((ia2 + ib2) & 8'hFF) : ((ia2 - ib2) & 8'hFF);
  let sum9 = {1'b0, ia2} + {1'b0, ib2};

  // Reset behavior (explicit, not disabled)
  assert property (@(posedge clk) (!reset) |-> (a_shifted==8'h00 && b_shifted==8'h00 && result==8'h00 && out==8'h00));

  // Stage-1: inputs captured correctly
  assert property (a_shifted == $past(in_a, 1, !reset));
  assert property (b_shifted == $past(in_b, 1, !reset));

  // Stage-2: result computed from prior a/b and current select (mod 256)
  assert property (result == (select ? add8 : sub8));

  // Stage-3: out is bit-reverse of prior result
  assert property (out == { $past(result,1,!reset)[0], $past(result,1,!reset)[1], $past(result,1,!reset)[2],
                            $past(result,1,!reset)[3], $past(result,1,!reset)[4], $past(result,1,!reset)[5],
                            $past(result,1,!reset)[6], $past(result,1,!reset)[7] });

  // End-to-end: out equals bit-reverse of op(select@t-1, in@(t-2))
  assert property (out == { op8_stage2[0], op8_stage2[1], op8_stage2[2], op8_stage2[3],
                            op8_stage2[4], op8_stage2[5], op8_stage2[6], op8_stage2[7] });

  // Knownness: known inputs imply known output when valid
  assert property ( !$isunknown({sel1, ia2, ib2}) |-> !$isunknown(out) );

  // Functional coverage
  cover property ( sel1 );                                 // addition path used
  cover property ( !sel1 );                                // subtraction path used
  cover property ( sel1 && sum9[8] );                      // addition overflow (carry out)
  cover property ( !sel1 && (ia2 < ib2) );                 // subtraction underflow (borrow)
  cover property ( out == 8'h00 );                         // zero result observed

endmodule

bind bitwise_add_sub bitwise_add_sub_sva sva_inst();