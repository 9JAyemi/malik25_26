// SVA checker for wasca_nios2_gen2_0_cpu_nios2_oci_td_mode
module wasca_nios2_gen2_0_cpu_nios2_oci_td_mode_sva (
  input [8:0] ctrl,
  input [3:0] td_mode
);

  // Expected combinational mapping
  wire [3:0] exp_td = (ctrl == 9'h000) ? 4'h0 :
                      (ctrl == 9'h001) ? 4'h1 :
                      (ctrl == 9'h002) ? 4'h2 :
                      (ctrl == 9'h003) ? 4'h3 :
                      (ctrl == 9'h004) ? 4'h4 : 4'h0;

  // Correct decode at every change (combinational consistency)
  assert property (@(ctrl or td_mode) td_mode == exp_td)
    else $error("td_mode mismatch: ctrl=%0h td=%0h exp=%0h", ctrl, td_mode, exp_td);

  // No spurious td_mode change without ctrl change (glitch-free)
  assert property (@(ctrl or td_mode) !($changed(td_mode) && !$changed(ctrl)))
    else $error("td_mode changed without ctrl change: ctrl=%0h td=%0h", ctrl, td_mode);

  // No X/Zs on interface
  assert property (@(ctrl or td_mode) !$isunknown(ctrl))
    else $error("ctrl has X/Z: %b", ctrl);
  assert property (@(ctrl or td_mode) !$isunknown(td_mode))
    else $error("td_mode has X/Z: %b", td_mode);

  // td_mode stays within the enumerated set
  assert property (@(ctrl or td_mode) td_mode inside {4'h0,4'h1,4'h2,4'h3,4'h4})
    else $error("td_mode out of allowed set: %0h", td_mode);

  // Functional coverage: each explicit case and the default path
  cover property (@(ctrl or td_mode) ctrl==9'h000 && td_mode==4'h0);
  cover property (@(ctrl or td_mode) ctrl==9'h001 && td_mode==4'h1);
  cover property (@(ctrl or td_mode) ctrl==9'h002 && td_mode==4'h2);
  cover property (@(ctrl or td_mode) ctrl==9'h003 && td_mode==4'h3);
  cover property (@(ctrl or td_mode) ctrl==9'h004 && td_mode==4'h4);
  cover property (@(ctrl or td_mode) (ctrl > 9'h004) && td_mode==4'h0); // default bucket

endmodule

// Bind into DUT
bind wasca_nios2_gen2_0_cpu_nios2_oci_td_mode
  wasca_nios2_gen2_0_cpu_nios2_oci_td_mode_sva u_wasca_nios2_gen2_0_cpu_nios2_oci_td_mode_sva (.*);