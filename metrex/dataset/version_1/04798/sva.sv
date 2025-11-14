// SVA for dff_pn0: synchronous active-low reset, synchronous set, D capture with priority R(!)>S(1)>D

module dff_pn0_sva (input logic D, C, R, S, Q);
  default clocking cb @(posedge C); endclocking

  // Track valid past sample for $past()
  logic past_v;
  initial past_v = 0;
  always @(posedge C) past_v <= 1;

  // Golden functional check (concise complete spec)
  // Next-cycle Q equals mux of previous-cycle controls/inputs with priority: !R > S > D
  a_func: assert property (disable iff (!past_v)
    1'b1 |=> Q == ( !$past(R) ? 1'b0 : ( $past(S) ? 1'b1 : $past(D) ) )
  );

  // Branch-specific checks (priority and clarity)
  a_reset: assert property (disable iff (!past_v)  !$past(R)      |=> Q == 1'b0 );
  a_set:   assert property (disable iff (!past_v)   $past(R)&&$past(S) |=> Q == 1'b1 );
  a_data:  assert property (disable iff (!past_v)   $past(R)&&!$past(S)|=> Q == $past(D) );

  // Known-value checks when outputs should be constants or data is known
  a_no_x_const: assert property (disable iff (!past_v)
    (!$past(R)) or ($past(R)&&$past(S)) |=> !$isunknown(Q)
  );
  a_no_x_data_when_known: assert property (disable iff (!past_v)
    $past(R)&&!$past(S) && !$isunknown($past(D)) |=> (Q == $past(D) && !$isunknown(Q))
  );

  // Hold behavior (no spurious change when data equals current)
  a_hold: assert property (disable iff (!past_v)
    $past(R)&&!$past(S) && ($past(D) == $past(Q)) |=> Q == $past(Q)
  );

  // Coverage: exercise all branches and key transitions
  c_reset:      cover property (disable iff (!past_v)  !$past(R)                 ##1 Q==0 );
  c_set:        cover property (disable iff (!past_v)   $past(R)&&$past(S)       ##1 Q==1 );
  c_data_0:     cover property (disable iff (!past_v)   $past(R)&&!$past(S)&&$past(D)==0 ##1 Q==0 );
  c_data_1:     cover property (disable iff (!past_v)   $past(R)&&!$past(S)&&$past(D)==1 ##1 Q==1 );
  c_reset_wins: cover property (disable iff (!past_v)  !$past(R)&&$past(S)       ##1 Q==0 );
  c_hold:       cover property (disable iff (!past_v)   $past(R)&&!$past(S)&&$past(D)==$past(Q) ##1 Q==$past(Q) );
  c_toggle_via_set_then_reset: cover property (disable iff (!past_v)
    $past(R)&&$past(S) ##1 Q==1 ##1 !$past(R) ##1 Q==0
  );
endmodule

bind dff_pn0 dff_pn0_sva sva_i(.D(D), .C(C), .R(R), .S(S), .Q(Q));