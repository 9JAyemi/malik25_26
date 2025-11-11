// SVA for WcaDcOffset
// Bind into DUT; samples on negedge clock (matches DUT)
module WcaDcOffset_sva;

  // Clocking
  default clocking cb @(negedge clock); endclocking

  // Helpers
  function automatic signed [11:0] dcof(input signed [25:0] i);
    return i[25:14];
  endfunction
  function automatic signed [25:0] se12(input signed [11:0] x);
    return {{14{x[11]}}, x};
  endfunction

  // Combinational relations and basic sanity
  assert property ($signed(sigout) == $signed(sig_in) - $signed(dcoffset));
  assert property ($signed(dcoffset) == dcof(integrator[iqSel]));
  assert property (!$isunknown({strobe, iqSel, dcoffset, sigout}));

  // Reset behavior
  assert property (reset |-> (integrator[0]==26'sd0 && integrator[1]==26'sd0));
  assert property (reset |=> (integrator[0]==26'sd0 && integrator[1]==26'sd0));

  // Operational properties (ignore during reset)
  default disable iff (reset);

  // Hold when strobe is low
  assert property (!strobe |=> (integrator[0]==$past(integrator[0]) &&
                                integrator[1]==$past(integrator[1])));

  // Selected channel updates by se12(sigout), other channel holds
  assert property (strobe && (iqSel==1'b0) |=> integrator[0]-$past(integrator[0]) == se12($past(sigout)));
  assert property (strobe && (iqSel==1'b0) |=> integrator[1] == $past(integrator[1]));
  assert property (strobe && (iqSel==1'b1) |=> integrator[1]-$past(integrator[1]) == se12($past(sigout)));
  assert property (strobe && (iqSel==1'b1) |=> integrator[0] == $past(integrator[0]));

  // Equivalent explicit form using sig_in and previous integrator slice
  assert property (strobe && (iqSel==1'b0) |=> integrator[0] ==
                   $past(integrator[0]) + se12($signed($past(sig_in)) - dcof($past(integrator[0]))));
  assert property (strobe && (iqSel==1'b1) |=> integrator[1] ==
                   $past(integrator[1]) + se12($signed($past(sig_in)) - dcof($past(integrator[1]))));

  // Coverage
  cover property (reset ##1 !reset);
  cover property (strobe && iqSel==1'b0);
  cover property (strobe && iqSel==1'b1);
  cover property (strobe && iqSel==1'b0 ##1 strobe && iqSel==1'b1);
  cover property (strobe && iqSel==1'b1 ##1 strobe && iqSel==1'b0);
  cover property (strobe && sigout[11]==1'b1);
  cover property (strobe && sigout[11]==1'b0);
  cover property (dcoffset==12'sh7FF);
  cover property (dcoffset==12'sh800);

endmodule

bind WcaDcOffset WcaDcOffset_sva sva_inst();