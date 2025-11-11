// SVA for ac97_sout
// Bind file; checks load, shift, stream tie-off, drain-to-zero, and provides useful coverage.
`ifndef SYNTHESIS
module ac97_sout_sva;
  // Bound inside ac97_sout; direct access to internal regs/wires
  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Combinational tie
  ap_sdata_tie: assert property (sdata_out == slt0_r[15]);

  // Load behavior
  ap_ld_slt0 : assert property (so_ld |=> slt0_r  == $past(slt0));
  ap_ld_slt1 : assert property (so_ld |=> slt1_r  == $past(slt1));
  ap_ld_slt2 : assert property (so_ld |=> slt2_r  == $past(slt2));
  ap_ld_slt3 : assert property (so_ld |=> slt3_r  == $past(slt3));
  ap_ld_slt4 : assert property (so_ld |=> slt4_r  == $past(slt4));
  ap_ld_slt5 : assert property (so_ld |=> slt5_r  == 20'h0);
  ap_ld_slt6 : assert property (so_ld |=> slt6_r  == $past(slt6));
  ap_ld_slt7 : assert property (so_ld |=> slt7_r  == $past(slt7));
  ap_ld_slt8 : assert property (so_ld |=> slt8_r  == $past(slt8));
  ap_ld_slt9 : assert property (so_ld |=> slt9_r  == $past(slt9));
  ap_ld_slt10: assert property (so_ld |=> slt10_r == 20'h0);
  ap_ld_slt11: assert property (so_ld |=> slt11_r == 20'h0);
  ap_ld_slt12: assert property (so_ld |=> slt12_r == 20'h0);

  // Shift behavior (note: aligns with #1 NBA using $past)
  ap_sh_slt0 : assert property (!$past(so_ld) |-> slt0_r  == { $past(slt0_r[14:0]),  $past(slt1_r[19]) });
  ap_sh_slt1 : assert property (!$past(so_ld) |-> slt1_r  == { $past(slt1_r[18:0]),  $past(slt2_r[19]) });
  ap_sh_slt2 : assert property (!$past(so_ld) |-> slt2_r  == { $past(slt2_r[18:0]),  $past(slt3_r[19]) });
  ap_sh_slt3 : assert property (!$past(so_ld) |-> slt3_r  == { $past(slt3_r[18:0]),  $past(slt4_r[19]) });
  ap_sh_slt4 : assert property (!$past(so_ld) |-> slt4_r  == { $past(slt4_r[18:0]),  $past(slt5_r[19]) });
  ap_sh_slt5 : assert property (!$past(so_ld) |-> slt5_r  == { $past(slt5_r[18:0]),  $past(slt6_r[19]) });
  ap_sh_slt6 : assert property (!$past(so_ld) |-> slt6_r  == { $past(slt6_r[18:0]),  $past(slt7_r[19]) });
  ap_sh_slt7 : assert property (!$past(so_ld) |-> slt7_r  == { $past(slt7_r[18:0]),  $past(slt8_r[19]) });
  ap_sh_slt8 : assert property (!$past(so_ld) |-> slt8_r  == { $past(slt8_r[18:0]),  $past(slt9_r[19]) });
  ap_sh_slt9 : assert property (!$past(so_ld) |-> slt9_r  == { $past(slt9_r[18:0]),  $past(slt10_r[19]) });
  ap_sh_slt10: assert property (!$past(so_ld) |-> slt10_r == { $past(slt10_r[18:0]), $past(slt11_r[19]) });
  ap_sh_slt11: assert property (!$past(so_ld) |-> slt11_r == { $past(slt11_r[18:0]), $past(slt12_r[19]) });
  ap_sh_slt12: assert property (!$past(so_ld) |-> slt12_r == { $past(slt12_r[18:0]), 1'b0 });

  // Known/clean outputs (optional but useful)
  ap_known_out : assert property (!$isunknown({sdata_out, slt0_r[15]}));
  ap_known_regs: assert property (!$isunknown({slt0_r, slt1_r, slt2_r, slt3_r, slt4_r,
                                               slt5_r, slt6_r, slt7_r, slt8_r, slt9_r,
                                               slt10_r, slt11_r, slt12_r}));

  // After 256 shifts with no load, chain must drain to zero
  localparam int FRAME_BITS = 256;
  ap_drain_zero: assert property ( (!so_ld)[*FRAME_BITS]
                                  |=> {slt0_r, slt1_r, slt2_r, slt3_r, slt4_r,
                                       slt5_r, slt6_r, slt7_r, slt8_r, slt9_r,
                                       slt10_r, slt11_r, slt12_r} == '0 );

  // Coverage
  cp_frame_len      : cover property (so_ld ##1 (!so_ld)[*255] ##1 so_ld);
  cp_back_to_back_ld: cover property (so_ld ##1 so_ld);
  cp_nonzero_payload: cover property (so_ld && (|slt1 || |slt2 || |slt3 || |slt4 ||
                                                |slt6 || |slt7 || |slt8 || |slt9));
endmodule

bind ac97_sout ac97_sout_sva sva();
`endif