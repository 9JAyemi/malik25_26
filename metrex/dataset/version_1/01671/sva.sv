// Bind this SVA module to encoderDCAC
bind encoderDCAC encoderDCAC_sva u_encoderDCAC_sva();

module encoderDCAC_sva();

  default clocking cb @(posedge clk); endclocking

  // -------------------------
  // Interface invariants / pipelines
  // -------------------------
  // zds_d is a 4-stage shift register
  assert property (zds_d[1] == $past(zds_d[0],1,'0));
  assert property (zds_d[2] == $past(zds_d[1],1,'0));
  assert property (zds_d[3] == $past(zds_d[2],1,'0));

  // zdi_d is 1-cycle delayed zdi
  assert property (zdi_d == $past(zdi,1,'0));

  // ac_in saturation from zdi_d (evaluate using prior zdi_d due to NBA)
  assert property (
    ac_in ==
      ($past(zdi_d[12],1,'0) == $past(zdi_d[11],1,'0)
        ? $past(zdi_d[11:0],1,'0)
        : {~$past(zdi_d[11],1,'0), {$bits(ac_in)-1{$past(zdi_d[11],1,'0)}}})
  );

  // izero definition
  assert property (izero == (ac_in == '0));

  // -------------------------
  // Block_mem address control and content
  // -------------------------
  // WA reset/increment behavior
  assert property ($past(!en,1,'0) |-> block_mem_wa == '0);
  assert property ($past(en && stb,1,'0) |-> block_mem_wa == $past(block_mem_wa,1,'0) + 3'd1);
  assert property ($past(en && !stb,1,'0) |-> block_mem_wa == $past(block_mem_wa,1,'0));

  // WA save on first block write
  assert property ($past(stb && first_blocki,1,'0) |-> block_mem_wa_save == $past(block_mem_wa,1,'0));

  // RA reset/increment behavior
  assert property ($past(!en,1,'0) |-> block_mem_ra == '0);
  assert property ($past(en && zds,1,'0)
                   |-> block_mem_ra == ($past(first_blockz,1,'0) ? $past(block_mem_wa_save,1,'0)
                                                                : ($past(block_mem_ra,1,'0) + 3'd1)));
  assert property ($past(en && !zds,1,'0) |-> block_mem_ra == $past(block_mem_ra,1,'0));

  // Block_mem data write (next cycle readback at same address equals written payload)
  assert property (
    $past(stb,1,'0)
      |-> block_mem[$past(block_mem_wa,1,'0)] ==
          {$past(lasti,1,'0), $past(comp_lastinmbi,1,'0), $past(comp_colori,1,'0),
           $past(comp_firsti,1,'0), $past(comp_numberi,1,'0)}
  );

  // Comp outputs map to block_mem_o
  assert property (comp_numbero == block_mem_o[2:0]);
  assert property (comp_firsto  == block_mem_o[3]);
  assert property (comp_coloro  == block_mem_o[4]);
  assert property (comp_lastinmbo == block_mem_o[5]);
  assert property (lasto        == block_mem_o[6]);

  // -------------------------
  // DC/AC datapath pipeline
  // -------------------------
  // dc_diff0 capture on zds_d[0]
  assert property (
    $past(zds_d[0],1,'0)
      |-> dc_diff0 == ($past(comp_firsto,1,'0) ? 13'b0
                                               : $past(dc_mem[$past(comp_numbero,1,'0)],1,'0))
  );

  // dc_diff on zds_d[1]
  assert property ($past(zds_d[1],1,'0) |-> dc_diff == $past(zdi_d,1,'0) - $past(dc_diff0,1,'0));

  // dc_diff_limited combinational definition holds
  assert property (
    dc_diff_limited ==
      ((dc_diff[12] == dc_diff[11]) ? dc_diff[11:0]
                                    : {~dc_diff[11], {11{dc_diff[11]}}})
  );

  // dc_restored on zds_d[2]
  assert property (
    $past(zds_d[2],1,'0)
      |-> dc_restored == $past(dc_diff0,1,'0) +
                         {$past(dc_diff_limited[11],1,'0), $past(dc_diff_limited[11:0],1,'0)}
  );

  // dc_mem writeback on zds_d[3]
  assert property (
    $past(zds_d[3],1,'0)
      |-> dc_mem[$past(comp_numbero,1,'0)] == $past(dc_restored,1,'0)
  );

  // last update when DC_tosend
  assert property ($past(DC_tosend,1,'0) |-> last == $past(lasto,1,'0));

  // -------------------------
  // Control: DCACen and cntr
  // -------------------------
  // DCACen next state equation
  assert property (
    DCACen == $past(en && (pre_DCACen || (DCACen && (cntr != 6'h3f))),1,'0)
  );

  // cntr reset/increment depends on prior DCACen
  assert property ($past(!DCACen,1,'0) |-> cntr == 6'h00);
  assert property ($past( DCACen,1,'0) |-> cntr == $past(cntr,1,'0) + 6'd1);

  // -------------------------
  // Run-length counter and output enable
  // -------------------------
  // rll counter resets and increments
  assert property ($past(DC_tosend || !izero || !DCACen,1,'0) |-> rll_cntr == 6'h00);
  assert property ($past(!DC_tosend && izero && DCACen,1,'0)  |-> rll_cntr == $past(rll_cntr,1,'0) + 6'd1);

  // rll_out structure (definition check)
  assert property (rll_out == (((val_r[12] && !val_r[14]) || (ac_in != 12'b0)) && (rll_cntr != 6'b0)));

  // -------------------------
  // Framing and data vector formation
  // -------------------------
  // val_r update
  assert property (
    val_r ==
      $past( DC_tosend
               ? {en, comp_coloro, (comp_lastinmbo && lasto), dc_diff_limited}
               : {2'b00, (cntr == 6'h3f), ac_in}
           ,1,'0)
  );

  // was_nonzero_AC update
  assert property (was_nonzero_AC == $past(en && (ac_in != 12'b0) && DCACen,1,'0));

  // pre_dv stable definition and dv alignment
  assert property (pre_dv == (rll_out || val_r[14] || was_nonzero_AC));
  assert property (dv == $past(pre_dv,1,'0));

  // do formation when pre_dv (next cycle data)
  assert property (
    $past(pre_dv && rll_out,1,'0)
      |-> do == $past({3'b000, val_r[12], 6'b000000, rll_cntr},1,'0)
  );
  assert property (
    $past(pre_dv && !rll_out,1,'0)
      |-> do == $past({1'b1, val_r},1,'0)
  );

  // Top-bit consistency
  assert property ($past(pre_dv && rll_out,1,'0)  |-> do[15] == 1'b0);
  assert property ($past(pre_dv && !rll_out,1,'0) |-> do[15] == 1'b1);

  // -------------------------
  // Functional covers (concise)
  // -------------------------
  // Cover: start DCACen, count to 63, then stop
  cover property (
    en && pre_DCACen ##1 DCACen
      ##[1:$] (cntr == 6'h3f)
      ##1 !DCACen
  );

  // Cover: RLL burst producing rll_out and corresponding do format
  cover property (
    DCACen && izero && !DC_tosend ##1 izero [*3] ##1 rll_out ##1 pre_dv
  );

  // Cover: Non-RLL AC nonzero emits do with MSB=1
  cover property (
    DCACen && (ac_in != 12'b0) && !DC_tosend ##1 pre_dv && !rll_out ##1 (do[15] == 1'b1)
  );

  // Cover: DC send updates last and uses comp_* metadata
  cover property (
    DC_tosend && comp_coloro && comp_lastinmbo && lasto ##1 dv && (do[15] == 1'b1)
  );

endmodule