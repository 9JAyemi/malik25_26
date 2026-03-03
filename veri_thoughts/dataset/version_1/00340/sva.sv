// SVA for mux4_1
module mux4_1_sva (
  input logic [3:0] D0,
  input logic [3:0] D1,
  input logic [3:0] D2,
  input logic [3:0] D3,
  input logic       S0,
  input logic       S1,
  input logic [3:0] Y
);
  default clocking cb @(*); endclocking

  // Functional correctness (4-state exact match, including X propagation)
  a_func: assert property ( Y === (S1 ? (S0 ? D3 : D2) : (S0 ? D1 : D0)) )
    else $error("mux4_1 functional mismatch");

  // Non-interference: when a non-selected input changes (with selects and selected data stable), Y must not change
  a_iso_00: assert property ( (S1==0 && S0==0) && $stable({S1,S0}) && $stable(D0) && $changed({D1,D2,D3}) |-> ##0 $stable(Y) )
    else $error("Y changed while selecting D0 and only other inputs changed");
  a_iso_01: assert property ( (S1==0 && S0==1) && $stable({S1,S0}) && $stable(D1) && $changed({D0,D2,D3}) |-> ##0 $stable(Y) )
    else $error("Y changed while selecting D1 and only other inputs changed");
  a_iso_10: assert property ( (S1==1 && S0==0) && $stable({S1,S0}) && $stable(D2) && $changed({D0,D1,D3}) |-> ##0 $stable(Y) )
    else $error("Y changed while selecting D2 and only other inputs changed");
  a_iso_11: assert property ( (S1==1 && S0==1) && $stable({S1,S0}) && $stable(D3) && $changed({D0,D1,D2}) |-> ##0 $stable(Y) )
    else $error("Y changed while selecting D3 and only other inputs changed");

  // Coverage: hit each select combo with correct output
  c_sel_00: cover property ( (S1==0 && S0==0) && (Y===D0) );
  c_sel_01: cover property ( (S1==0 && S0==1) && (Y===D1) );
  c_sel_10: cover property ( (S1==1 && S0==0) && (Y===D2) );
  c_sel_11: cover property ( (S1==1 && S0==1) && (Y===D3) );

  // Coverage: when selected data changes (with stable selects), Y changes in the same sample
  c_follow_00: cover property ( (S1==0 && S0==0) && $stable({S1,S0}) && $changed(D0) ##0 $changed(Y) );
  c_follow_01: cover property ( (S1==0 && S0==1) && $stable({S1,S0}) && $changed(D1) ##0 $changed(Y) );
  c_follow_10: cover property ( (S1==1 && S0==0) && $stable({S1,S0}) && $changed(D2) ##0 $changed(Y) );
  c_follow_11: cover property ( (S1==1 && S0==1) && $stable({S1,S0}) && $changed(D3) ##0 $changed(Y) );

endmodule

// Bind into all mux4_1 instances
bind mux4_1 mux4_1_sva mux4_1_sva_i (.*);