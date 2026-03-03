// SVA for sum_2_msb
module sum_2_msb_sva(input [3:0] in_4, input [1:0] out_2);

  // Clock on any input bit edge (combinational sampling)
  default clocking cb @(
    posedge in_4[0] or negedge in_4[0] or
    posedge in_4[1] or negedge in_4[1] or
    posedge in_4[2] or negedge in_4[2] or
    posedge in_4[3] or negedge in_4[3]
  ); endclocking

  // Known-ness: when MSBs are known, output must be known
  assert property (!$isunknown(in_4[3:2]) |-> !$isunknown(out_2));

  // Functional correctness: out == {OR(MSBs), OR(MSBs)} when MSBs known
  assert property (!$isunknown(in_4[3:2]) |-> (out_2 == {2{in_4[3] | in_4[2]}}));

  // Duplicate bits constraint when output known
  assert property (!$isunknown(out_2) |-> (out_2[1] == out_2[0]));

  // Independence: LSB changes must not affect output when MSBs known
  assert property (( !$isunknown(in_4[3:2]) && $changed(in_4[1:0]) ) |-> $stable(out_2));

  // Functional coverage of all MSB combinations and corresponding outputs
  cover property ((in_4[3:2]==2'b00) && (out_2==2'b00));
  cover property ((in_4[3:2]==2'b01) && (out_2==2'b11));
  cover property ((in_4[3:2]==2'b10) && (out_2==2'b11));
  cover property ((in_4[3:2]==2'b11) && (out_2==2'b11));

  // Toggle coverage of MSBs and LSB-independence observation
  cover property ($rose(in_4[3]));
  cover property ($fell(in_4[3]));
  cover property ($rose(in_4[2]));
  cover property ($fell(in_4[2]));
  cover property ($changed(in_4[1:0]) && $stable(out_2));

  // Output toggles track OR(MSBs)
  cover property (($past(in_4[3]|in_4[2])==0) && ((in_4[3]|in_4[2])==1) && $rose(out_2[0]) && $rose(out_2[1]));
  cover property (($past(in_4[3]|in_4[2])==1) && ((in_4[3]|in_4[2])==0) && $fell(out_2[0]) && $fell(out_2[1]));

endmodule

// Bind into DUT
// synthesis translate_off
bind sum_2_msb sum_2_msb_sva u_sum_2_msb_sva (.*);
// synthesis translate_on