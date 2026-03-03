// SVA for altpcierd_icm_sideband
module altpcierd_icm_sideband_sva (
  input             clk,
  input             rstn,

  // inputs
  input    [12:0]   cfg_busdev,
  input    [31:0]   cfg_devcsr,
  input    [31:0]   cfg_linkcsr,
  input    [31:0]   cfg_prmcsr,
  input    [23:0]   cfg_tcvcmap,
  input    [15:0]   cfg_msicsr,
  input    [4:0]    pex_msi_num,
  input             app_int_sts,
  input             app_int_sts_ack,
  input    [2:0]    cpl_err,
  input             cpl_pending,

  // registered outputs
  input    [12:0]   cfg_busdev_del,
  input    [31:0]   cfg_devcsr_del,
  input    [31:0]   cfg_linkcsr_del,
  input    [31:0]   cfg_prmcsr_del,
  input    [23:0]   cfg_tcvcmap_del,
  input    [15:0]   cfg_msicsr_del,
  input             app_int_sts_del,
  input             app_int_sts_ack_del,
  input    [4:0]    pex_msi_num_del,
  input    [2:0]    cpl_err_del,
  input             cpl_pending_del
);

  default clocking cb @ (posedge clk); endclocking

  // Reset values must be 0 while rstn==0 (checked every clk)
  ap_reset_values: assert property (
    !rstn |->
      (cfg_busdev_del  === 13'h0) &&
      (cfg_devcsr_del  === 32'h0) &&
      (cfg_linkcsr_del === 32'h0) &&
      (cfg_prmcsr_del  === 32'h0) &&
      (cfg_tcvcmap_del === 24'h0) &&
      (cfg_msicsr_del  === 16'h0) &&
      (app_int_sts_del === 1'b0 ) &&
      (app_int_sts_ack_del === 1'b0) &&
      (pex_msi_num_del === 5'h0 ) &&
      (cpl_err_del     === 3'h0 ) &&
      (cpl_pending_del === 1'b0 )
  );

  // One-cycle pipeline (only when both current and previous cycles are out of reset)
  ap_pipe_delay: assert property (
    rstn && $past(rstn) |->
      (cfg_busdev_del   === $past(cfg_busdev))   &&
      (cfg_devcsr_del   === $past(cfg_devcsr))   &&
      (cfg_linkcsr_del  === $past(cfg_linkcsr))  &&
      (cfg_prmcsr_del   === $past(cfg_prmcsr))   &&
      (cfg_tcvcmap_del  === $past(cfg_tcvcmap))  &&
      (cfg_msicsr_del   === $past(cfg_msicsr))   &&
      (app_int_sts_del  === $past(app_int_sts))  &&
      (app_int_sts_ack_del === $past(app_int_sts_ack)) &&
      (pex_msi_num_del  === $past(pex_msi_num))  &&
      (cpl_err_del      === $past(cpl_err))      &&
      (cpl_pending_del  === $past(cpl_pending))
  );

  // Coverage: reset release seen
  cp_reset_release: cover property ($rose(rstn));

  // Coverage: each path exercised with a visible transfer after an input change
  cp_cfg_busdev   : cover property (rstn && $past(rstn) && $changed(cfg_busdev)   |=> cfg_busdev_del   === $past(cfg_busdev));
  cp_devcsr       : cover property (rstn && $past(rstn) && $changed(cfg_devcsr)   |=> cfg_devcsr_del   === $past(cfg_devcsr));
  cp_linkcsr      : cover property (rstn && $past(rstn) && $changed(cfg_linkcsr)  |=> cfg_linkcsr_del  === $past(cfg_linkcsr));
  cp_prmcsr       : cover property (rstn && $past(rstn) && $changed(cfg_prmcsr)   |=> cfg_prmcsr_del   === $past(cfg_prmcsr));
  cp_tcvcmap      : cover property (rstn && $past(rstn) && $changed(cfg_tcvcmap)  |=> cfg_tcvcmap_del  === $past(cfg_tcvcmap));
  cp_msicsr       : cover property (rstn && $past(rstn) && $changed(cfg_msicsr)   |=> cfg_msicsr_del   === $past(cfg_msicsr));
  cp_app_int_sts  : cover property (rstn && $past(rstn) && $changed(app_int_sts)  |=> app_int_sts_del  === $past(app_int_sts));
  cp_app_int_ack  : cover property (rstn && $past(rstn) && $changed(app_int_sts_ack) |=> app_int_sts_ack_del === $past(app_int_sts_ack));
  cp_msi_num      : cover property (rstn && $past(rstn) && $changed(pex_msi_num)  |=> pex_msi_num_del  === $past(pex_msi_num));
  cp_cpl_err      : cover property (rstn && $past(rstn) && $changed(cpl_err)      |=> cpl_err_del      === $past(cpl_err));
  cp_cpl_pend     : cover property (rstn && $past(rstn) && $changed(cpl_pending)  |=> cpl_pending_del  === $past(cpl_pending));

endmodule

// Bind into the DUT
bind altpcierd_icm_sideband altpcierd_icm_sideband_sva u_altpcierd_icm_sideband_sva (.*);