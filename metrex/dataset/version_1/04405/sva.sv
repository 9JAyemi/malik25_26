// SVA for axi_hdmi_tx_vdma
// Bind into the DUT to access internal signals
module axi_hdmi_tx_vdma_sva_bind;
  // local copies of thresholds (match DUT localparams)
  localparam int unsigned BUF_THRESHOLD_LO = 9'd3;
  localparam int unsigned BUF_THRESHOLD_HI = 9'd509;
  localparam int unsigned RDY_THRESHOLD_LO = 9'd450;
  localparam int unsigned RDY_THRESHOLD_HI = 9'd500;

  // helper: gray-to-binary (9-bit) for checking
  function automatic [8:0] g2b9(input [8:0] g);
    reg [8:0] b;
    begin
      b[8]=g[8]; b[7]=b[8]^g[7]; b[6]=b[7]^g[6]; b[5]=b[6]^g[5];
      b[4]=b[5]^g[4]; b[3]=b[4]^g[3]; b[2]=b[3]^g[2]; b[1]=b[2]^g[1]; b[0]=b[1]^g[0];
      g2b9=b;
    end
  endfunction

  default clocking cb @(posedge vdma_clk); endclocking
  // Disable during reset for most checks
  default disable iff (vdma_rst);

  // Synchronizer chain for hdmi_fs_toggle
  assert property (1 |=> vdma_fs_toggle_m1 == $past(hdmi_fs_toggle));
  assert property (1 |=> vdma_fs_toggle_m2 == $past(vdma_fs_toggle_m1));
  assert property (1 |=> vdma_fs_toggle_m3 == $past(vdma_fs_toggle_m2));
  // fs pulse is XOR of the two delayed taps (registered relationship)
  assert property (1 |=> vdma_fs == ($past(vdma_fs_toggle_m2) ^ $past(vdma_fs_toggle_m3)));
  // fs is single-cycle pulse
  assert property (vdma_fs |=> !vdma_fs);

  // fs_ret capture and toggle
  assert property (vdma_fs_ret |=> vdma_fs_waddr == $past(vdma_waddr));
  assert property (vdma_fs_ret |=> vdma_fs_ret_toggle == ~$past(vdma_fs_ret_toggle));

  // Write handshake and address/data path
  assert property (1 |=> vdma_wr == ($past(vdma_valid) & $past(vdma_ready)));
  assert property ($past(vdma_wr) |=> vdma_waddr == ($past(vdma_waddr) + 9'd1));
  assert property (!$past(vdma_wr) |=> vdma_waddr == $past(vdma_waddr));
  assert property (1 |=> vdma_wdata == { $past(vdma_data[55:32]), $past(vdma_data[23:0]) });

  // TPM generator/checker
  // Reset on rst or fs_ret
  assert property ((vdma_rst || vdma_fs_ret) |=> (vdma_tpm_data == 23'd0 && vdma_tpm_oos == 1'b0));
  // Increment and OOS update happen one cycle after write (due to NBA order)
  assert property (disable iff (vdma_fs_ret) $past(vdma_wr) |=> vdma_tpm_data == ($past(vdma_tpm_data) + 23'd1));
  assert property (disable iff (vdma_fs_ret) !$past(vdma_wr) |=> vdma_tpm_data == $past(vdma_tpm_data));
  assert property ($past(vdma_wr) |=> vdma_tpm_oos == $past(vdma_wdata != vdma_tpm_data_s));
  assert property (!$past(vdma_wr) |=> vdma_tpm_oos == $past(vdma_tpm_oos));

  // Gray-domain read address synchronization and conversion
  assert property (1 |=> vdma_raddr_g_m1 == $past(hdmi_raddr_g));
  assert property (1 |=> vdma_raddr_g_m2 == $past(vdma_raddr_g_m1));
  assert property (1 |=> vdma_raddr == g2b9($past(vdma_raddr_g_m2)));

  // Address difference register
  assert property (1 |=> vdma_addr_diff == $past(({1'b1, vdma_waddr} - vdma_raddr)[8:0]));

  // Ready hysteresis
  assert property ((vdma_addr_diff >= RDY_THRESHOLD_HI) |=> vdma_ready == 1'b0);
  assert property ((vdma_addr_diff <= RDY_THRESHOLD_LO) |=> vdma_ready == 1'b1);
  assert property ((vdma_addr_diff > RDY_THRESHOLD_LO && vdma_addr_diff < RDY_THRESHOLD_HI) |=> vdma_ready == $past(vdma_ready));

  // Almost-full/empty flags
  assert property ((vdma_addr_diff > BUF_THRESHOLD_HI) |=> vdma_almost_full == 1'b1);
  assert property (!(vdma_addr_diff > BUF_THRESHOLD_HI) |=> vdma_almost_full == 1'b0);
  assert property ((vdma_addr_diff < BUF_THRESHOLD_LO) |=> vdma_almost_empty == 1'b1);
  assert property (!(vdma_addr_diff < BUF_THRESHOLD_LO) |=> vdma_almost_empty == 1'b0);

  // Overflow/Underflow flags follow their combinational precursors (registered next cycle)
  assert property (1 |=> vdma_ovf == $past((vdma_addr_diff < BUF_THRESHOLD_LO) ? vdma_almost_full   : 1'b0));
  assert property (1 |=> vdma_unf == $past((vdma_addr_diff > BUF_THRESHOLD_HI) ? vdma_almost_empty : 1'b0));

  // Basic X checks on key outputs when out of reset
  assert property (!$isunknown({vdma_wr, vdma_ready, vdma_waddr, vdma_wdata, vdma_fs, vdma_tpm_oos, vdma_ovf, vdma_unf}));

  // Coverage
  cover property (vdma_wr);
  cover property (vdma_ready ##1 !vdma_ready ##1 vdma_ready);
  cover property (vdma_fs);
  cover property (vdma_ovf);
  cover property (vdma_unf);
  cover property (vdma_tpm_oos);
endmodule

bind axi_hdmi_tx_vdma axi_hdmi_tx_vdma_sva_bind sva_i();