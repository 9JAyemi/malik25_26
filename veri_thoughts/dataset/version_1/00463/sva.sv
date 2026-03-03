// SVA checker for sky130_fd_sc_hd__a41oi
// Function: Y = ~(B1 | (A1 & A2 & A3 & A4))

module a41oi_sva (
  input logic Y,
  input logic A1, A2, A3, A4,
  input logic B1
);
  default clocking cb @(*); endclocking

  // Functional correctness
  ap_func: assert property ( Y === ~(B1 | (A1 & A2 & A3 & A4)) )
    else $error("a41oi func mismatch");

  // X-propagation: if inputs known, output must be known
  ap_known: assert property ( !$isunknown({A1,A2,A3,A4,B1}) |-> !$isunknown(Y) )
    else $error("a41oi X-propagation issue");

  // Dominance checks (redundant to ap_func but good for debug localization)
  ap_b1_dom:   assert property ( B1 |-> (Y == 1'b0) ) else $error("B1 dominance fail");
  ap_and_dom:  assert property ( (A1 & A2 & A3 & A4) |-> (Y == 1'b0) ) else $error("AND4 dominance fail");
  ap_pass:     assert property ( (!B1 && !(A1 & A2 & A3 & A4)) |-> (Y == 1'b1) ) else $error("pass-through fail");

  // Coverage: all meaningful output causes and toggles
  c_y1:        cover property ( !B1 && !(A1 & A2 & A3 & A4) && Y );
  c_y0_b1:     cover property ( B1 && !Y );
  c_y0_and:    cover property ( !B1 && (A1 & A2 & A3 & A4) && !Y );
  c_y_rise:    cover property ( @(posedge Y) 1'b1 );
  c_y_fall:    cover property ( @(negedge Y) 1'b1 );

endmodule

// Bind into all instances of the DUT
bind sky130_fd_sc_hd__a41oi a41oi_sva a41oi_sva_i(.*);