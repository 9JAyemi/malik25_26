// SVA for axi_hdmi_tx_vdma
// Bind this module to the DUT for assertions and coverage

module axi_hdmi_tx_vdma_sva;

  // Clock/Reset
  default clocking cb @(posedge vdma_clk); endclocking
  default disable iff (vdma_rst);

  // Gray->Binary helper (for SVA)
  function automatic [8:0] g2b_sva(input [8:0] g);
    automatic logic [8:0] b;
    begin
      b[8]=g[8];
      b[7]=b[8]^g[7];
      b[6]=b[7]^g[6];
      b[5]=b[6]^g[5];
      b[4]=b[5]^g[4];
      b[3]=b[4]^g[3];
      b[2]=b[3]^g[2];
      b[1]=b[2]^g[1];
      b[0]=b[1]^g[0];
      return b;
    end
  endfunction

  // Asynchronous reset effects (checked during reset)
  assert property (@(posedge vdma_clk) vdma_rst |-> (vdma_fs_toggle_m1==1'b0 && vdma_fs_toggle_m2==1'b0 && vdma_fs_toggle_m3==1'b0));
  assert property (@(posedge vdma_clk) vdma_rst |-> (vdma_raddr_g_m1==9'd0 && vdma_raddr_g_m2==9'd0));
  assert property (@(posedge vdma_clk) vdma_rst |=> (vdma_waddr==9'd0));
  assert property (@(posedge vdma_clk) (vdma_rst or vdma_fs_ret) |=> (vdma_tpm_data==23'd0 && vdma_tpm_oos==1'b0));

  // CDC pipelines
  assert property (vdma_fs_toggle_m1 == $past(hdmi_fs_toggle));
  assert property (vdma_fs_toggle_m2 == $past(vdma_fs_toggle_m1));
  assert property (vdma_fs_toggle_m3 == $past(vdma_fs_toggle_m2));
  assert property (vdma_raddr_g_m1   == $past(hdmi_raddr_g));
  assert property (vdma_raddr_g_m2   == $past(vdma_raddr_g_m1));

  // Frame start pulse generation and return handshake
  assert property (vdma_fs == $past(vdma_fs_toggle_m2 ^ vdma_fs_toggle_m3));
  assert property (vdma_fs |=> !vdma_fs); // one-cycle pulse
  assert property (vdma_fs_ret |=> vdma_fs_waddr == $past(vdma_waddr));
  assert property (vdma_fs_ret |=> vdma_fs_ret_toggle == ~$past(vdma_fs_ret_toggle));
  assert property ($changed(vdma_fs_ret_toggle) |-> vdma_fs_ret);

  // Write handshake and address/data path
  assert property (vdma_wr == $past(vdma_valid && vdma_ready));
  assert property ((vdma_valid && vdma_ready) |=> vdma_wr);
  assert property (vdma_wr |=> vdma_waddr == $past(vdma_waddr) + 9'd1);
  assert property (!vdma_wr |=> vdma_waddr == $past(vdma_waddr));
  assert property (vdma_wdata == $past({vdma_data[55:32], vdma_data[23:0]}));

  // Read address decode and address difference
  assert property (vdma_raddr == $past(g2b_sva(vdma_raddr_g_m2)));
  assert property (vdma_addr_diff == $past(({1'b1, vdma_waddr} - vdma_raddr)[8:0]));

  // Ready hysteresis (RDY_THRESHOLD_LO=450, RDY_THRESHOLD_HI=500)
  assert property ((vdma_addr_diff >= 9'd500) |=> vdma_ready==1'b0);
  assert property ((vdma_addr_diff <= 9'd450) |=> vdma_ready==1'b1);
  assert property ((vdma_addr_diff > 9'd450 && vdma_addr_diff < 9'd500) |=> vdma_ready==$past(vdma_ready));

  // Almost-full/empty (BUF_THRESHOLD_LO=3, BUF_THRESHOLD_HI=509)
  assert property (vdma_almost_full  == $past(vdma_addr_diff > 9'd509));
  assert property (vdma_almost_empty == $past(vdma_addr_diff < 9'd3));

  // Overflow/Underflow flags (registered from prior cycle's conditions)
  assert property (vdma_ovf == $past((vdma_addr_diff < 9'd3)   ? vdma_almost_full  : 1'b0));
  assert property (vdma_unf == $past((vdma_addr_diff > 9'd509) ? vdma_almost_empty : 1'b0));
  assert property (!(vdma_ovf && vdma_unf));

  // TPM generator/checker behavior
  assert property (vdma_wr |=> vdma_tpm_data == $past(vdma_tpm_data) + 23'd1);
  assert property (!vdma_wr && !vdma_fs_ret |=> vdma_tpm_data == $past(vdma_tpm_data));
  assert property (vdma_wr |=> vdma_tpm_oos == ($past(vdma_wdata) != { $past(vdma_tpm_data), 1'b1, $past(vdma_tpm_data), 1'b0 }));
  assert property (!vdma_wr && !vdma_fs_ret |=> vdma_tpm_oos == $past(vdma_tpm_oos));
  assert property (vdma_tpm_oos && !$past(vdma_tpm_oos) |-> $past(vdma_wr) && ($past(vdma_wdata) != { $past(vdma_tpm_data), 1'b1, $past(vdma_tpm_data), 1'b0 }));

  // Coverage
  cover property (vdma_fs);
  cover property (vdma_fs_ret && $changed(vdma_fs_ret_toggle));
  cover property (vdma_valid && !vdma_ready ##1 vdma_valid && vdma_ready ##1 vdma_wr);
  cover property (vdma_addr_diff == 9'd450 ##1 vdma_ready);
  cover property (vdma_addr_diff == 9'd500 ##1 !vdma_ready);
  cover property (vdma_almost_full  && vdma_addr_diff > 9'd509);
  cover property (vdma_almost_empty && vdma_addr_diff < 9'd3);
  cover property (vdma_ovf);
  cover property (vdma_unf);
  cover property (vdma_wr && vdma_waddr==9'h1FF ##1 vdma_wr && vdma_waddr==9'h000);
  cover property (vdma_wr && vdma_tpm_oos);

endmodule

bind axi_hdmi_tx_vdma axi_hdmi_tx_vdma_sva u_axi_hdmi_tx_vdma_sva();