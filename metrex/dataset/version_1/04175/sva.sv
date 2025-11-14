// SVA for three_input_and_gate (NAND3)
module three_input_and_gate_sva;

  // Functional equivalence and internal consistency
  a_func:        assert property (@(*) output1 === ~(input1 & input2 & input3))
                  else $error("NAND3 functional mismatch");
  a_int1:        assert property (@(*) intermediate1 === (input1 & input2))
                  else $error("intermediate1 != input1 & input2");
  a_int2:        assert property (@(*) intermediate2 === (intermediate1 & input3))
                  else $error("intermediate2 != intermediate1 & input3");
  a_consistent:  assert property (@(*) output1 === ~intermediate2)
                  else $error("output1 != ~intermediate2");

  // No X/Z on internal/output when inputs are known
  a_no_x:        assert property (@(*)
                    (!$isunknown({input1,input2,input3})) |->
                    (!$isunknown({intermediate1,intermediate2,output1}))
                  ) else $error("X/Z on internal/output with known inputs");

  // Truth-table coverage (all 8 combinations)
  c_000: cover property (@(*) (input1==0 && input2==0 && input3==0 && output1==1));
  c_001: cover property (@(*) (input1==0 && input2==0 && input3==1 && output1==1));
  c_010: cover property (@(*) (input1==0 && input2==1 && input3==0 && output1==1));
  c_011: cover property (@(*) (input1==0 && input2==1 && input3==1 && output1==1));
  c_100: cover property (@(*) (input1==1 && input2==0 && input3==0 && output1==1));
  c_101: cover property (@(*) (input1==1 && input2==0 && input3==1 && output1==1));
  c_110: cover property (@(*) (input1==1 && input2==1 && input3==0 && output1==1));
  c_111: cover property (@(*) (input1==1 && input2==1 && input3==1 && output1==0));

  // Toggle coverage on internal and output due to any input edge
  c_o_r: cover property (@(posedge input1 or posedge input2 or posedge input3 or
                           negedge input1 or negedge input2 or negedge input3) $rose(output1));
  c_o_f: cover property (@(posedge input1 or posedge input2 or posedge input3 or
                           negedge input1 or negedge input2 or negedge input3) $fell(output1));
  c_i1_r: cover property (@(posedge input1 or posedge input2 or posedge input3 or
                            negedge input1 or negedge input2 or negedge input3) $rose(intermediate1));
  c_i1_f: cover property (@(posedge input1 or posedge input2 or posedge input3 or
                            negedge input1 or negedge input2 or negedge input3) $fell(intermediate1));
  c_i2_r: cover property (@(posedge input1 or posedge input2 or posedge input3 or
                            negedge input1 or negedge input2 or negedge input3) $rose(intermediate2));
  c_i2_f: cover property (@(posedge input1 or posedge input2 or posedge input3 or
                            negedge input1 or negedge input2 or negedge input3) $fell(intermediate2));

endmodule

bind three_input_and_gate three_input_and_gate_sva sva();