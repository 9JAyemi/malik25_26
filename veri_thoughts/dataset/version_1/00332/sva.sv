// SVA checker for sky130_fd_sc_hd__a21oi (Y = ~(B1 | (A1 & A2)))
module a21oi_sva (input logic A1, A2, B1, Y);

  // Sample on any data change; ##0 lets logic settle in the same timestep
  default clocking cb @(A1 or A2 or B1 or Y); endclocking

  // 4-state functional equivalence (includes X/Z propagation correctness)
  property p_func; ##0 (Y === ~(B1 | (A1 & A2))); endproperty
  assert property (p_func)
    else $error("a21oi func mismatch: Y=%b A1=%b A2=%b B1=%b", Y,A1,A2,B1);

  // If inputs are known 0/1, output must be known
  property p_no_x_if_known_inputs; ##0 (!$isunknown({A1,A2,B1})) |-> !$isunknown(Y); endproperty
  assert property (p_no_x_if_known_inputs)
    else $error("a21oi unexpected X/Z on Y with known inputs: Y=%b A1=%b A2=%b B1=%b", Y,A1,A2,B1);

  // Truth-table coverage (cover only when all signals are known and correct)
  cover property (##0 (!($isunknown({A1,A2,B1,Y})) && A1==0 && A2==0 && B1==0 && Y==1));
  cover property (##0 (!($isunknown({A1,A2,B1,Y})) && A1==0 && A2==0 && B1==1 && Y==0));
  cover property (##0 (!($isunknown({A1,A2,B1,Y})) && A1==0 && A2==1 && B1==0 && Y==1));
  cover property (##0 (!($isunknown({A1,A2,B1,Y})) && A1==0 && A2==1 && B1==1 && Y==0));
  cover property (##0 (!($isunknown({A1,A2,B1,Y})) && A1==1 && A2==0 && B1==0 && Y==1));
  cover property (##0 (!($isunknown({A1,A2,B1,Y})) && A1==1 && A2==0 && B1==1 && Y==0));
  cover property (##0 (!($isunknown({A1,A2,B1,Y})) && A1==1 && A2==1 && B1==0 && Y==0));
  cover property (##0 (!($isunknown({A1,A2,B1,Y})) && A1==1 && A2==1 && B1==1 && Y==0));

  // Sanity: observe both output values
  cover property (##0 (Y===1'b0));
  cover property (##0 (Y===1'b1));

endmodule

// Bind to the DUT
bind sky130_fd_sc_hd__a21oi a21oi_sva a21oi_sva_i (.*);