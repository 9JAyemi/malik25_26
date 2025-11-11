// SVA checker for MPUC1307
module MPUC1307_sva #(parameter int total_bits = 32) ();
  default clocking cb @(posedge CLK); endclocking

  // Stall behavior when ED is low
  a_stall: assert property (!ED |=> $stable({edd,edd2,edd3,mpyjd,mpyjd2,mpyjd3,
                                             dx5,dx7,dt,dii,doo,droo,DOR,DOI})));

  // Control pipelines advance when ED is high
  a_ctl_edd0:   assert property (ED |=> edd  == DS);
  a_ctl_edd1:   assert property (ED |=> edd2 == $past(edd));
  a_ctl_edd2:   assert property (ED |=> edd3 == $past(edd2));
  a_ctl_mpy0:   assert property (ED |=> mpyjd  == MPYJ);
  a_ctl_mpy1:   assert property (ED |=> mpyjd2 == $past(mpyjd));
  a_ctl_mpy2:   assert property (ED |=> mpyjd3 == $past(mpyjd2));

  // Data-path select/computation when ED is high
  a_dp_sel_ds:  assert property (ED && DS  |=> (dx5 == (DR + (DR << 2))) &&
                                             (dx7 == (DR - (DR >>> 3))) &&
                                             (dt  ==  DR) &&
                                             (dii ==  DI));
  a_dp_sel_dii: assert property (ED && !DS |=> (dx5 == (dii + (dii << 2))) &&
                                             (dx7 == (dii - (dii >>> 3))) &&
                                             (dt  ==  dii) &&
                                             (dii ==  $past(dii)));

  // Combinational equations (always hold)
  a_dx5p: assert property (1'b1 |-> dx5p == ((dx5 << 1) + (dx7 >>> 1)));
  a_dot:  assert property (1'b1 |-> dot  == (dx5p + (dt >>> 6) - (dx5 >>> 13)));

  // doo/droo register updates under ED
  a_doo:  assert property (ED |=> doo  == (dot >>> 3));
  a_droo: assert property (ED |=> droo == $past(doo));

  // Output update rules (only when ED and edd3)
  a_out_mpyj:  assert property (ED && edd3 && mpyjd3  |=> (DOR == doo) && (DOI == -$past(droo)));
  a_out_nompy: assert property (ED && edd3 && !mpyjd3 |=> (DOR == $past(droo)) && (DOI == doo));
  a_out_hold:  assert property (ED && !edd3 |=> $stable({DOR,DOI}));

  // Basic functional coverage
  c_ed_ds:     cover property (ED && DS);
  c_ed_nods:   cover property (ED && !DS);
  c_ed_low:    cover property (!ED);
  c_pipe_mature: cover property (ED[*3] ##1 edd3);
  c_out_mpy:   cover property (ED && edd3 && mpyjd3);
  c_out_nompy: cover property (ED && edd3 && !mpyjd3);
  c_dr_neg:    cover property (DR[total_bits-1]);
  c_di_neg:    cover property (DI[total_bits-1]);
endmodule

bind MPUC1307 MPUC1307_sva #(.total_bits(total_bits)) i_MPUC1307_sva();