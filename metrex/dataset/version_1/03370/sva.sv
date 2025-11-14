// SVA for sp_mux_4to1_sel2_7_1
// Bindable, clockless via $global_clock, concise but thorough on functionality, X-prop, and coverage.

module sp_mux_4to1_sel2_7_1_sva;
  default clocking cb @(posedge $global_clock); endclocking

  // Functional correctness for known selects (bit-accurate, incl. X bits in data)
  ap_sel00: assert property ( (din5 === 2'b00) |-> (dout === din1) );
  ap_sel01: assert property ( (din5 === 2'b01) |-> (dout === din2) );
  ap_sel10: assert property ( (din5 === 2'b10) |-> (dout === din3) );
  ap_sel11: assert property ( (din5 === 2'b11) |-> (dout === din4) );

  // X-resolution expectations (when ambiguity is removable by equal data)
  ap_x_lsb_low:  assert property ( (din5[1] === 1'b0) && $isunknown(din5[0]) && (din1 === din2) |-> (dout === din1) );
  ap_x_lsb_high: assert property ( (din5[1] === 1'b1) && $isunknown(din5[0]) && (din3 === din4) |-> (dout === din3) );
  ap_x_msb_sel0: assert property ( (din5[0] === 1'b0) && $isunknown(din5[1]) && (din1 === din3) |-> (dout === din1) );
  ap_x_msb_sel1: assert property ( (din5[0] === 1'b1) && $isunknown(din5[1]) && (din2 === din4) |-> (dout === din2) );
  ap_x_both:     assert property ( $isunknown(din5) && (din1===din2) && (din1===din3) && (din1===din4) |-> (dout === din1) );

  // Internal signal sanity (structural consistency with RTL)
  ap_alias_sel:  assert property ( sel === din5 );
  ap_m1_0:       assert property ( mux_1_0 === ( (din5[0] == 0) ? din1 : din2 ) );
  ap_m1_1:       assert property ( mux_1_1 === ( (din5[0] == 0) ? din3 : din4 ) );
  ap_m2_0:       assert property ( mux_2_0 === ( (din5[1] == 0) ? mux_1_0 : mux_1_1 ) );
  ap_dout_alias: assert property ( dout === mux_2_0 );

  // Functional coverage
  cp_sel00: cover property (din5===2'b00);
  cp_sel01: cover property (din5===2'b01);
  cp_sel10: cover property (din5===2'b10);
  cp_sel11: cover property (din5===2'b11);
  cp_drive1: cover property (dout===din1);
  cp_drive2: cover property (dout===din2);
  cp_drive3: cover property (dout===din3);
  cp_drive4: cover property (dout===din4);
endmodule

bind sp_mux_4to1_sel2_7_1 sp_mux_4to1_sel2_7_1_sva sva_i();