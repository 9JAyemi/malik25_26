// SVA for module cheat
checker cheat_sva;
  default clocking cb @(posedge clk); endclocking
  default disable iff ($initstate);

  // Basic sanity
  assert property (!$isunknown({data_out, cheat_hit, snescmd_unlock}));

  // Address match sanity
  assert property ($onehot0(nmi_match_bits));
  assert property ($onehot0(irq_match_bits));
  assert property ($onehot0(rst_match_bits));
  // At most one cheat match (avoid ambiguous priority)
  assert property ($onehot0(cheat_match_bits));

  // data_out priority: cheats [0..5]
  assert property (cheat_match_bits[0] |-> data_out == cheat_data[0]);
  assert property (cheat_match_bits[1] & ~cheat_match_bits[0] |-> data_out == cheat_data[1]);
  assert property (cheat_match_bits[2] & ~|cheat_match_bits[1:0] |-> data_out == cheat_data[2]);
  assert property (cheat_match_bits[3] & ~|cheat_match_bits[2:0] |-> data_out == cheat_data[3]);
  assert property (cheat_match_bits[4] & ~|cheat_match_bits[3:0] |-> data_out == cheat_data[4]);
  assert property (cheat_match_bits[5] & ~|cheat_match_bits[4:0] |-> data_out == cheat_data[5]);
  // data_out priority: vectors and fallbacks
  assert property (!cheat_addr_match & nmi_match_bits[1] |-> data_out == 8'h04);
  assert property (!cheat_addr_match & !nmi_match_bits[1] & irq_match_bits[1] |-> data_out == 8'h04);
  assert property (!cheat_addr_match & !(nmi_match_bits[1] | irq_match_bits[1]) & rst_match_bits[1] |-> data_out == 8'h6b);
  assert property (!cheat_addr_match & !(|{nmi_match_bits[1], irq_match_bits[1], rst_match_bits[1]}) & nmicmd_enable |-> data_out == nmicmd);
  assert property (!cheat_addr_match & !(|{nmi_match_bits[1], irq_match_bits[1], rst_match_bits[1], nmicmd_enable}) & return_vector_enable |-> data_out == return_vector);
  assert property (!cheat_addr_match & !(|{nmi_match_bits[1], irq_match_bits[1], rst_match_bits[1], nmicmd_enable, return_vector_enable}) & branch1_enable |-> data_out == branch1_offset);
  assert property (!cheat_addr_match & !(|{nmi_match_bits[1], irq_match_bits[1], rst_match_bits[1], nmicmd_enable, return_vector_enable, branch1_enable}) & branch2_enable |-> data_out == branch2_offset);
  assert property (!cheat_addr_match & !(|{nmi_match_bits[1], irq_match_bits[1], rst_match_bits[1], nmicmd_enable, return_vector_enable, branch1_enable, branch2_enable}) |-> data_out == 8'h2a);

  // cheat_hit equivalence (causes <-> effect)
  localparam int unsigned _0 = 0;
  wire cause_snescmd = (snescmd_unlock & hook_enable_sync & (nmicmd_enable | return_vector_enable | branch1_enable | branch2_enable));
  wire cause_reset   = (reset_unlock & rst_addr_match);
  wire cause_cheat   = (cheat_enable & cheat_addr_match);
  wire cause_vectors = (hook_enable_sync &
                        (((auto_nmi_enable_sync & nmi_enable) & nmi_addr_match & vector_unlock) |
                         ((auto_irq_enable_sync & irq_enable) & irq_addr_match & vector_unlock)));
  assert property (cause_snescmd or cause_reset or cause_cheat or cause_vectors |-> cheat_hit);
  assert property (cheat_hit |-> (cause_snescmd or cause_reset or cause_cheat or cause_vectors));

  // Vector unlock behavior
  assert property (SNES_rd_strobe
                   & hook_enable_sync
                   & (((auto_nmi_enable_sync & nmi_enable) & nmi_match_bits[1]) |
                      ((auto_irq_enable_sync & irq_enable) & irq_match_bits[1]))
                   & (cpu_push_cnt == 3'd4)
                   |=> vector_unlock_r == 2'b11);
  assert property (vector_unlock == (|vector_unlock_r));

  // Reset unlock behavior
  assert property (SNES_reset_strobe |=> reset_unlock_r == 2'b11);
  assert property (SNES_cycle_start & rst_addr_match & (|reset_unlock_r) |=> reset_unlock_r == $past(reset_unlock_r) - 1);
  assert property (!(SNES_reset_strobe | (SNES_cycle_start & rst_addr_match & (|reset_unlock_r))) |=> reset_unlock_r == $past(reset_unlock_r));
  assert property (reset_unlock == (|reset_unlock_r));

  // snescmd_unlock behavior
  assert property (SNES_reset_strobe |=> (!snescmd_unlock_r && !snescmd_unlock));
  assert property (SNES_rd_strobe
                   & hook_enable_sync
                   & (((auto_nmi_enable_sync & nmi_enable) & nmi_match_bits[1]) |
                      ((auto_irq_enable_sync & irq_enable) & irq_match_bits[1]))
                   & (cpu_push_cnt == 3'd4)
                   |=> snescmd_unlock);
  assert property (SNES_rd_strobe & rst_match_bits[1] & (|reset_unlock_r) |=> snescmd_unlock);
  // Disable strobe is one-cycle pulse and eventually clears unlock
  assert property (snescmd_unlock_disable_strobe |-> ##1 !snescmd_unlock_disable_strobe);
  assert property ($rose(snescmd_unlock_disable_strobe) |-> ##[1:150] !snescmd_unlock);

  // Hook enable count and hook_enable
  assert property (((snescmd_unlock & snescmd_wr_strobe & ~|SNES_ADDR[8:0] & (SNES_DATA == 8'h85)) |
                    (holdoff_enable & SNES_reset_strobe))
                   |=> hook_enable_count == 30'd960000000);
  assert property ((|hook_enable_count) |-> !hook_enable);
  assert property ((!|hook_enable_count) |-> hook_enable);

  // sync_delay and sync copies
  assert property (SNES_cycle_start & (nmi_addr_match | irq_addr_match) |=> sync_delay == 2'b10);
  assert property (SNES_cycle_start & !(nmi_addr_match | irq_addr_match) & (|sync_delay) |=> sync_delay == $past(sync_delay) - 1);
  assert property (SNES_cycle_start & !(nmi_addr_match | irq_addr_match) & (sync_delay == 2'b00)
                   |=> auto_nmi_enable_sync == $past(auto_nmi_enable)
                    && auto_irq_enable_sync == $past(auto_irq_enable)
                    && hook_enable_sync     == $past(hook_enable));

  // usage_count and auto-{nmi,irq} selection
  assert property (usage_count == $past(usage_count) - 1);
  assert property ((usage_count != 21'b0) & SNES_cycle_start & nmi_match_bits[0] |=> nmi_usage == $past(nmi_usage) + 1);
  assert property ((usage_count != 21'b0) & SNES_cycle_start & irq_match_bits[0] |=> irq_usage == $past(irq_usage) + 1);
  assert property ((usage_count == 21'b0) |-> (nmi_usage == (SNES_cycle_start & nmi_match_bits[1])) && (irq_usage == (SNES_cycle_start & irq_match_bits[1])));
  assert property ((usage_count == 21'b0) & (|$past(nmi_usage) & |$past(irq_usage)) |=> (auto_nmi_enable && !auto_irq_enable));
  assert property ((usage_count == 21'b0) & ($past(irq_usage) == 5'b0)             |=> (auto_nmi_enable && !auto_irq_enable));
  assert property ((usage_count == 21'b0) & ($past(nmi_usage) == 5'b0)             |=> (!auto_nmi_enable && auto_irq_enable));

  // snescmd control writes at addr 0
  assert property (snescmd_unlock & snescmd_wr_strobe & ~|SNES_ADDR[8:0] & (SNES_DATA == 8'h82) |=> cheat_enable);
  assert property (snescmd_unlock & snescmd_wr_strobe & ~|SNES_ADDR[8:0] & (SNES_DATA == 8'h83) |=> !cheat_enable);
  assert property (snescmd_unlock & snescmd_wr_strobe & ~|SNES_ADDR[8:0] & (SNES_DATA == 8'h84) |=> {nmi_enable, irq_enable} == 2'b00);

  // Programming interface
  assert property (pgm_we & (pgm_idx < 3'd6) |=> (cheat_addr[pgm_idx] == $past(pgm_in[31:8])) && (cheat_data[pgm_idx] == $past(pgm_in[7:0])));
  assert property (pgm_we & (pgm_idx == 3'd6) |=> cheat_enable_mask == $past(pgm_in[5:0]));
  assert property (pgm_we & (pgm_idx == 3'd7)
                   |=> {wram_present, buttons_enable, holdoff_enable, irq_enable, nmi_enable, cheat_enable}
                       == (($past({wram_present, buttons_enable, holdoff_enable, irq_enable, nmi_enable, cheat_enable}) & ~ $past(pgm_in[13:8]))
                           | $past(pgm_in[5:0])));

  // Pad capture
  assert property (snescmd_wr_strobe & (SNES_ADDR[8:0] == 9'h1f0) |=> pad_data[7:0]  == $past(SNES_DATA));
  assert property (snescmd_wr_strobe & (SNES_ADDR[8:0] == 9'h1f1) |=> pad_data[15:8] == $past(SNES_DATA));

  // nmicmd decode
  assert property (pad_data == 16'h3030 |-> nmicmd == 8'h80);
  assert property (pad_data == 16'h2070 |-> nmicmd == 8'h81);
  assert property (pad_data == 16'h10b0 |-> nmicmd == 8'h82);
  assert property (pad_data == 16'h9030 |-> nmicmd == 8'h83);
  assert property (pad_data == 16'h5030 |-> nmicmd == 8'h84);
  assert property (pad_data == 16'h1070 |-> nmicmd == 8'h85);
  assert property (!(pad_data inside {16'h3030,16'h2070,16'h10b0,16'h9030,16'h5030,16'h1070}) |-> nmicmd == 8'h00);

  // branch1_offset combinational behavior (key cases)
  assert property (buttons_enable & snes_ajr & (nmicmd != 8'h00) |-> branch1_offset == 8'h30);
  assert property (buttons_enable & snes_ajr & (nmicmd == 8'h00) & branch_wram |-> branch1_offset == 8'h3a);
  assert property (buttons_enable & snes_ajr & (nmicmd == 8'h00) & !branch_wram |-> branch1_offset == 8'h3d);
  assert property (buttons_enable & !snes_ajr & pad_latch & branch_wram |-> branch1_offset == 8'h3a);
  assert property (buttons_enable & !snes_ajr & pad_latch & !branch_wram |-> branch1_offset == 8'h3d);
  assert property (buttons_enable & !snes_ajr & !pad_latch |-> branch1_offset == 8'h00);
  assert property (!buttons_enable & branch_wram |-> branch1_offset == 8'h3a);
  assert property (!buttons_enable & !branch_wram |-> branch1_offset == 8'h3d);

  // branch2_offset combinational behavior
  assert property (nmicmd == 8'h81 |-> branch2_offset == 8'h0e);
  assert property ((nmicmd != 8'h81) & branch_wram |-> branch2_offset == 8'h00);
  assert property ((nmicmd != 8'h81) & !branch_wram |-> branch2_offset == 8'h03);

  // Coverage: key scenarios
  cover property (cheat_enable & cheat_addr_match & SNES_cycle_start);
  cover property (SNES_rd_strobe & hook_enable_sync & auto_nmi_enable_sync & nmi_enable & nmi_match_bits[1] & (cpu_push_cnt==3'd4) & cheat_hit);
  cover property (SNES_rd_strobe & rst_match_bits[1] & (|reset_unlock_r) & cheat_hit);
  cover property (!cheat_addr_match & !(|{nmi_match_bits[1],irq_match_bits[1],rst_match_bits[1],nmicmd_enable,return_vector_enable,branch1_enable,branch2_enable}) ##1 data_out == 8'h2a);
  cover property (snescmd_unlock & snescmd_wr_strobe & (SNES_ADDR[8:0] == 9'h1fd) ##[1:100] !snescmd_unlock);
  cover property (pgm_we & (pgm_idx==3'd0));
  cover property (pgm_we & (pgm_idx==3'd6));
  cover property (pgm_we & (pgm_idx==3'd7));
  cover property (buttons_enable & snes_ajr & (nmicmd!=8'h00) & (branch1_offset==8'h30));
endchecker

bind cheat cheat_sva chk();