// Drop this SVA block inside img_delay_ctl (or bind to it) after the DUT code.

`ifdef SVA
  default clocking cb @(posedge clk); endclocking

  logic past_valid;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // time_cnt: reset on eof, else increment
  assert property (disable iff (!past_valid)
    time_cnt == ( $past(eof) ? '0 : $past(time_cnt) + 1 )
  );

  // delay0_pulse: asserted exactly when (prev) time_cnt == delay0_cnt and prev eof==0
  assert property (disable iff (!past_valid)
    delay0_pulse == ( !$past(eof) && ($past(time_cnt) == $past(delay0_cnt)) )
  );

  // one-cycle pulse and at most one pulse before next eof
  assert property (disable iff (!past_valid) !(delay0_pulse && $past(delay0_pulse)));
  assert property (disable iff (!past_valid) delay0_pulse |-> (!delay0_pulse until_with eof));

  // Shift register behavior
  assert property (disable iff (!past_valid)
    history_pos[1] == ( $past(delay0_pulse) ? $past(cur_pos) : $past(history_pos[1]) )
  );
  genvar gi;
  generate
    for (gi = 2; gi < C_MAX_FRMN; gi++) begin : hist_shift_chk
      assert property (disable iff (!past_valid)
        history_pos[gi] == ( $past(delay0_pulse) ? $past(history_pos[gi-1]) : $past(history_pos[gi]) )
      );
    end
  endgenerate

  // hisAcur_pos mapping
  assert property (hisAcur_pos[0] == cur_pos);
  generate
    for (gi = 1; gi < C_MAX_FRMN; gi++) begin : map_chk
      assert property (hisAcur_pos[gi] == history_pos[gi]);
    end
  endgenerate

  // movie_pos update and hold
  assert property (disable iff (!past_valid)
    movie_pos == ( $past(delay0_pulse)
                   ? $past(hisAcur_pos[$past(delay0_frm)])
                   : $past(movie_pos) )
  );

  // Index must be known when used
  assert property (disable iff (!past_valid)
    $past(delay0_pulse) |-> !$isunknown($past(delay0_frm))
  );

  // Basic coverage
  cover property (delay0_pulse);
  generate
    for (gi = 0; gi < C_MAX_FRMN; gi++) begin : cov_frm_sel
      cover property ( $past(delay0_pulse) && ($past(delay0_frm) == gi[C_FRMN_WIDTH-1:0]) );
    end
  endgenerate
`endif