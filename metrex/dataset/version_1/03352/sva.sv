// SVA for module cheat
// Bind this module or paste inside cheat under a synthesis-off guard.
bind cheat cheat_sva();

module cheat_sva;

  default clocking cb @(posedge clk); endclocking

  // Basic combinational equivalences
  assert property (cheat_addr_match == (|cheat_match_bits));
  assert property (nmi_addr_match   == (|nmi_match_bits));
  assert property (irq_addr_match   == (|irq_match_bits));
  assert property (hook_enable      == (~|hook_enable_count & ~hook_disable));
  assert property (snescmd_unlock   == (&unlock_token | temp_vector_unlock));

  // cheat_match_bits must be masked
  genvar mi;
  generate
    for (mi=0; mi<6; mi++) begin : g_mask
      assert property (!cheat_enable_mask[mi] |-> !cheat_match_bits[mi]);
    end
  endgenerate

  // data_out priority chain
  assert property (cheat_match_bits[0] |-> data_out==cheat_data[0]);
  assert property (!cheat_match_bits[0] && cheat_match_bits[1] |-> data_out==cheat_data[1]);
  assert property (!(|cheat_match_bits[1:0]) && cheat_match_bits[2] |-> data_out==cheat_data[2]);
  assert property (!(|cheat_match_bits[2:0]) && cheat_match_bits[3] |-> data_out==cheat_data[3]);
  assert property (!(|cheat_match_bits[3:0]) && cheat_match_bits[4] |-> data_out==cheat_data[4]);
  assert property (!(|cheat_match_bits[4:0]) && cheat_match_bits[5] |-> data_out==cheat_data[5]);
  assert property (!(|cheat_match_bits) && nmi_match_bits[1] |-> data_out==8'hb0);
  assert property (!(|cheat_match_bits) && !nmi_match_bits[1] && irq_match_bits[1] |-> data_out==8'hc4);
  assert property (!(|cheat_match_bits) && !nmi_match_bits[1] && !irq_match_bits[1] |-> data_out==8'h2b);

  // cheat_hit exact definition
  assert property (cheat_hit ==
                   ((cheat_enable & cheat_addr_match) |
                    (hook_enable_sync &
                     (((auto_nmi_enable_sync & nmi_enable) & nmi_addr_match) |
                      ((auto_irq_enable_sync & irq_enable) & irq_addr_match)))));

  // usage_count free-running down-counter (mod 2^21)
  assert property ($past(usage_count,1,cb)=== $past(usage_count,1,cb) ? 1'b1 :
                   1'b1); // guard for X on first cycle
  assert property (!$isunknown($past(usage_count)) |-> usage_count == $past(usage_count) - 21'd1);

  // nmi/irq usage increments when counting (usage_count != 0)
  assert property ($past(usage_count)!=21'd0 && $past(SNES_cycle_start) &&
                   $past(nmi_match_bits[0]) && !$past(hook_disable)
                   |-> nmi_usage == $past(nmi_usage)+5'd1);
  assert property ($past(usage_count)!=21'd0 && $past(SNES_cycle_start) &&
                   $past(irq_match_bits[0]) && !$past(hook_disable)
                   |-> irq_usage == $past(irq_usage)+5'd1);

  // nmi/irq usage seeding when window ends (usage_count==0)
  assert property ($past(usage_count)==21'd0
                   |-> nmi_usage == ({4'b0, ( ~$past(hook_disable) & $past(SNES_cycle_start) & $past(nmi_match_bits[1]) )})
                   &&  irq_usage == ({4'b0, ( ~$past(hook_disable) & $past(SNES_cycle_start) & $past(irq_match_bits[1]) )}));

  // auto enable selection on window end (based on previous usage snapshot)
  assert property ($past(usage_count)==21'd0 && (|$past(nmi_usage) && |$past(irq_usage))
                   |-> auto_nmi_enable && !auto_irq_enable);
  assert property ($past(usage_count)==21'd0 && ($past(irq_usage)==5'd0)
                   |-> auto_nmi_enable && !auto_irq_enable);
  assert property ($past(usage_count)==21'd0 && ($past(nmi_usage)==5'd0)
                   |-> !auto_nmi_enable && auto_irq_enable);

  // temp vector unlock timing
  assert property ($past(SNES_cycle_start) && ($past(nmi_addr_match) || $past(irq_addr_match))
                   |-> temp_unlock_delay==7'd72 && temp_vector_unlock);
  assert property ($past(SNES_cycle_start) && !$past(nmi_addr_match) && !$past(irq_addr_match) &&
                   $past(temp_unlock_delay)!=7'd0
                   |-> temp_unlock_delay == $past(temp_unlock_delay)-7'd1);
  assert property ($past(SNES_cycle_start) && !$past(nmi_addr_match) && !$past(irq_addr_match) &&
                   $past(temp_unlock_delay)==7'd0
                   |-> temp_vector_unlock==1'b0);

  // sync_delay pipeline and sampling of *_sync and hook_enable_sync
  assert property ($past(SNES_cycle_start) && ($past(nmi_addr_match) || $past(irq_addr_match))
                   |-> sync_delay==2'b10);
  assert property ($past(SNES_cycle_start) && !$past(nmi_addr_match) && !$past(irq_addr_match) &&
                   $past(sync_delay)!=2'b00
                   |-> sync_delay == $past(sync_delay)-2'd1);
  assert property ($past(SNES_cycle_start) && !$past(nmi_addr_match) && !$past(irq_addr_match) &&
                   $past(sync_delay)==2'b00
                   |-> auto_nmi_enable_sync==$past(auto_nmi_enable) &&
                       auto_irq_enable_sync==$past(auto_irq_enable) &&
                       hook_enable_sync==$past(hook_enable));

  // Unlock token behavior
  // Correct bytes set corresponding bit
  assert property ($past(snescmd_wr_strobe) && $past(SNES_ADDR[8:0])==9'h1f4 && $past(SNES_DATA)==8'h48
                   |-> unlock_token[0]);
  assert property ($past(snescmd_wr_strobe) && $past(SNES_ADDR[8:0])==9'h1f5 && $past(SNES_DATA)==8'h75
                   |-> unlock_token[1]);
  assert property ($past(snescmd_wr_strobe) && $past(SNES_ADDR[8:0])==9'h1f6 && $past(SNES_DATA)==8'h72
                   |-> unlock_token[2]);
  assert property ($past(snescmd_wr_strobe) && $past(SNES_ADDR[8:0])==9'h1f7 && $past(SNES_DATA)==8'h7a
                   |-> unlock_token[3]);

  // Any other write in 0x1F4..0x1F7 clears the token
  assert property ($past(snescmd_wr_strobe) &&
                   $past(SNES_ADDR[8:2])==9'b1111101 &&
                   !((($past(SNES_ADDR[8:0])==9'h1f4) && ($past(SNES_DATA)==8'h48)) ||
                     (($past(SNES_ADDR[8:0])==9'h1f5) && ($past(SNES_DATA)==8'h75)) ||
                     (($past(SNES_ADDR[8:0])==9'h1f6) && ($past(SNES_DATA)==8'h72)) ||
                     (($past(SNES_ADDR[8:0])==9'h1f7) && ($past(SNES_DATA)==8'h7a)))
                   |-> unlock_token==4'b0000);

  // Reset clears token
  assert property ($past(SNES_reset_strobe) |-> unlock_token==4'b0000);

  // snescmd config writes (require unlock)
  assert property ($past(snescmd_unlock) && $past(snescmd_wr_strobe) && $past(~|SNES_ADDR[8:0]) && $past(SNES_DATA)==8'h82
                   |-> cheat_enable);
  assert property ($past(snescmd_unlock) && $past(snescmd_wr_strobe) && $past(~|SNES_ADDR[8:0]) && $past(SNES_DATA)==8'h83
                   |-> !cheat_enable);
  assert property ($past(snescmd_unlock) && $past(snescmd_wr_strobe) && $past(~|SNES_ADDR[8:0]) && $past(SNES_DATA)==8'h84
                   |-> !nmi_enable && !irq_enable);

  // hook_disable write (require unlock)
  assert property ($past(snescmd_unlock) && $past(snescmd_wr_strobe) && $past(SNES_ADDR[8:0])==9'h1fd
                   |-> hook_disable == $past(SNES_DATA[0]));

  // hook_enable_count load/decrement
  assert property (($past(snescmd_unlock) && $past(snescmd_wr_strobe) && $past(~|SNES_ADDR[8:0]) && $past(SNES_DATA)==8'h85) ||
                   ($past(holdoff_enable) && $past(SNES_reset_strobe))
                   |-> hook_enable_count == 30'd880000000);
  assert property (!( ($past(snescmd_unlock) && $past(snescmd_wr_strobe) && $past(~|SNES_ADDR[8:0]) && $past(SNES_DATA)==8'h85) ||
                      ($past(holdoff_enable) && $past(SNES_reset_strobe)) ) &&
                   $past(hook_enable_count)!=30'd0
                   |-> hook_enable_count == $past(hook_enable_count)-30'd1);

  // hook_enable reflects count==0 and not disabled
  assert property (hook_disable |-> !hook_enable);
  assert property ((hook_enable_count!=0) |-> !hook_enable);

  // Programming interface (pgm_we)
  genvar i;
  generate
    for (i=0; i<6; i++) begin : g_prog
      assert property ($past(pgm_we) && $past(pgm_idx)==i[2:0]
                       |-> cheat_addr[i]==$past(pgm_in[31:8]) && cheat_data[i]==$past(pgm_in[7:0]));
    end
  endgenerate
  assert property ($past(pgm_we) && $past(pgm_idx)==3'd6
                   |-> cheat_enable_mask == $past(pgm_in[5:0]));
  assert property ($past(pgm_we) && $past(pgm_idx)==3'd7
                   |-> {holdoff_enable, irq_enable, nmi_enable, cheat_enable}
                       == ( $past({holdoff_enable, irq_enable, nmi_enable, cheat_enable}) & ~ $past(pgm_in[7:4]) )
                          | $past(pgm_in[3:0]));

  // Coverage

  // Typical unlock sequence then unlock high
  sequence ubyte (addr, data);
    snescmd_wr_strobe && SNES_ADDR[8:0]==addr && SNES_DATA==data;
  endsequence
  cover property (ubyte(9'h1f4,8'h48) ##[0:16]
                  ubyte(9'h1f5,8'h75) ##[0:16]
                  ubyte(9'h1f6,8'h72) ##[0:16]
                  ubyte(9'h1f7,8'h7a) ##1 snescmd_unlock);

  // Hook timer load via command
  cover property (snescmd_unlock && snescmd_wr_strobe && ~|SNES_ADDR[8:0] && SNES_DATA==8'h85 ##1 hook_enable_count==30'd880000000);

  // Hook timer load via reset+holdoff
  cover property (holdoff_enable && SNES_reset_strobe ##1 hook_enable_count==30'd880000000);

  // NMI vector path hit
  cover property (hook_enable_sync && auto_nmi_enable_sync && nmi_enable && nmi_addr_match && cheat_hit);

  // IRQ vector path hit
  cover property (hook_enable_sync && auto_irq_enable_sync && irq_enable && irq_addr_match && cheat_hit);

  // Cheat direct hit
  cover property (cheat_enable && cheat_addr_match && cheat_hit);

  // data_out default case
  cover property (!cheat_addr_match && !nmi_match_bits[1] && !irq_match_bits[1] && data_out==8'h2b);

  // Sync sampling event
  cover property ($past(SNES_cycle_start) && !$past(nmi_addr_match) && !$past(irq_addr_match) &&
                  $past(sync_delay)==2'b00 ##1
                  (auto_nmi_enable_sync==$past(auto_nmi_enable) && hook_enable_sync==$past(hook_enable)));

endmodule