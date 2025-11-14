// SVA checker for memory_module
module memory_module_sva;

  // Bind-time visibility into DUT scope (uses DUT signal names directly)
  default clocking cb @(posedge cpu_clock); endclocking

  logic past_valid;
  always @(posedge cpu_clock) past_valid <= 1'b1;

  wire update_cond = memreg_rd || (volports_enabled && port_wr);

  // Power-up/init checks (from DUT initial block)
  initial begin
    assert (snd_wrtoggle === 1'b0);
    assert (snd_datnvol  === 1'b1);
    assert (mode_8chans  === 1'b0);
  end

  // Toggle on update, hold otherwise
  property p_toggle_on_update;
    disable iff (!past_valid)
    update_cond |=> (snd_wrtoggle != $past(snd_wrtoggle));
  endproperty
  assert property (p_toggle_on_update);

  property p_hold_no_update;
    disable iff (!past_valid)
    !update_cond |=> (snd_wrtoggle == $past(snd_wrtoggle)) &&
                     (snd_datnvol  == $past(snd_datnvol))  &&
                     (snd_addr     == $past(snd_addr))     &&
                     (snd_data     == $past(snd_data));
  endproperty
  assert property (p_hold_no_update);

  // Memory read branch (has priority)
  property p_mem_read;
    disable iff (!past_valid)
    memreg_rd |=> (snd_datnvol == 1'b1) &&
                  (snd_data    == {7'b0, $past(din)}) &&
                  ( ($past(mode_8chans)==1'b0 && snd_addr == {1'b0, $past(a[9:8])}) ||
                    ($past(mode_8chans)==1'b1 && snd_addr ==        $past(a[10:8])) );
  endproperty
  assert property (p_mem_read);

  // Volume port write branch (only when memreg_rd=0)
  property p_vol_write;
    disable iff (!past_valid)
    (volports_enabled && port_wr && !memreg_rd) |=> (snd_datnvol == 1'b0) &&
                                                    (snd_addr    == $past(volnum)) &&
                                                    (snd_data    == {7'b0, $past(din)});
  endproperty
  assert property (p_vol_write);

  // Data zero-extend check on any update
  property p_data_zero_extend;
    disable iff (!past_valid)
    update_cond |=> (snd_data[7:1] == 7'b0) && (snd_data[0] == $past(din));
  endproperty
  assert property (p_data_zero_extend);

  // Explicit priority when both fire
  property p_priority_both;
    disable iff (!past_valid)
    (memreg_rd && volports_enabled && port_wr) |=> (snd_datnvol == 1'b1);
  endproperty
  assert property (p_priority_both);

  // No unknowns driven on update cycles
  property p_no_x_on_update;
    disable iff (!past_valid)
    update_cond |-> !$isunknown({snd_wrtoggle, snd_datnvol, snd_addr, snd_data});
  endproperty
  assert property (p_no_x_on_update);

  // Coverage
  cover property (memreg_rd);
  cover property (volports_enabled && port_wr && !memreg_rd);
  cover property (memreg_rd && volports_enabled && port_wr);        // overlap priority
  cover property (update_cond ##1 update_cond);                     // back-to-back updates
  cover property (!update_cond)[*3];                                // idle stretch
  cover property (memreg_rd && mode_8chans==1'b0);                  // 4-ch mode read
  cover property (memreg_rd && mode_8chans==1'b1);                  // 8-ch mode read

endmodule

bind memory_module memory_module_sva sva_inst();