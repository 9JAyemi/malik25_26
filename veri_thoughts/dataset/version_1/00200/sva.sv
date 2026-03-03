// SVA checker for sky130_fd_sc_hd__nor4
module sky130_fd_sc_hd__nor4_sva (input logic Y, A, B, C, D);

  // Sample on any input edge
  default clocking cb @ (posedge A or negedge A or
                         posedge B or negedge B or
                         posedge C or negedge C or
                         posedge D or negedge D); endclocking

  // 4-state functional correctness
  assert property (Y === ~(A | B | C | D));

  // Deterministic cases
  assert property ((A===1 || B===1 || C===1 || D===1) |-> (Y === 1'b0));
  assert property ((A===0 && B===0 && C===0 && D===0) |-> (Y === 1'b1));

  // X-propagation when no '1' present and at least one input is X/Z
  assert property ((!(A===1 || B===1 || C===1 || D===1) && $isunknown({A,B,C,D})) |-> $isunknown(Y));

  // No high-Z on output
  assert property (Y !== 1'bz);

  // Single-input 0->1 with others 0 forces Y 1->0 (combinational timing)
  assert property (($rose(A) && $past(B===0 && C===0 && D===0) && $past(Y)===1) |-> (Y===0));
  assert property (($rose(B) && $past(A===0 && C===0 && D===0) && $past(Y)===1) |-> (Y===0));
  assert property (($rose(C) && $past(A===0 && B===0 && D===0) && $past(Y)===1) |-> (Y===0));
  assert property (($rose(D) && $past(A===0 && B===0 && C===0) && $past(Y)===1) |-> (Y===0));

  // Functional coverage: all input combinations and both Y values
  cover property ({A,B,C,D} === 4'b0000);
  cover property ({A,B,C,D} === 4'b0001);
  cover property ({A,B,C,D} === 4'b0010);
  cover property ({A,B,C,D} === 4'b0011);
  cover property ({A,B,C,D} === 4'b0100);
  cover property ({A,B,C,D} === 4'b0101);
  cover property ({A,B,C,D} === 4'b0110);
  cover property ({A,B,C,D} === 4'b0111);
  cover property ({A,B,C,D} === 4'b1000);
  cover property ({A,B,C,D} === 4'b1001);
  cover property ({A,B,C,D} === 4'b1010);
  cover property ({A,B,C,D} === 4'b1011);
  cover property ({A,B,C,D} === 4'b1100);
  cover property ({A,B,C,D} === 4'b1101);
  cover property ({A,B,C,D} === 4'b1110);
  cover property ({A,B,C,D} === 4'b1111);

  cover property (Y===1'b1);
  cover property (Y===1'b0);

endmodule

// Bind into DUT
bind sky130_fd_sc_hd__nor4 sky130_fd_sc_hd__nor4_sva nor4_sva_i (.*);