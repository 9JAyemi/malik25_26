// SystemVerilog Assertions for csconvert_mono, csconvert_jp4, csconvert_jp4diff
// Concise, focused on key behavior, next-state relations, pipelines, muxing, and coverage.

// ======================= csconvert_mono =======================
module csconvert_mono_sva (
  input  logic        en,
  input  logic        clk,
  input  logic [7:0]  din,
  input  logic        pre_first_in,
  input  logic [7:0]  y_out,
  input  logic [7:0]  yaddr,
  input  logic        ywe,
  input  logic        pre_first_out
);
  default clocking cb @(posedge clk); endclocking
  logic past_valid; always_ff @(posedge clk) past_valid <= 1'b1;

  // Combinational outputs
  assert property (y_out == {~din[7], din[6:0]});
  assert property (pre_first_out == pre_first_in);

  // ywe next-state relation
  assert property (disable iff(!past_valid)
    ywe == ($past(en) & ($past(pre_first_in) | ($past(ywe) & ($past(yaddr) != 8'hff))))
  );

  // yaddr next-state relation
  assert property (disable iff(!past_valid)
    (!$past(en) || $past(pre_first_in)) |-> (yaddr == 8'h00)
  );
  assert property (disable iff(!past_valid)
    ($past(en) && !$past(pre_first_in) && $past(ywe)) |-> (yaddr == $past(yaddr) + 8'h01)
  );
  assert property (disable iff(!past_valid)
    ($past(en) && !$past(pre_first_in) && !$past(ywe)) |-> (yaddr == $past(yaddr))
  );

  // Wrap behavior at 0xff (increment still occurs, then ywe drops unless pre_first_in)
  assert property (disable iff(!past_valid)
    ($past(ywe) && ($past(yaddr) == 8'hff)) |-> (yaddr == 8'h00)
  );

  // Coverage: full burst, wrap, and deassert
  cover property (disable iff(!past_valid)
    en ##1 pre_first_in ##1 ywe [*1:$] ##0 (yaddr == 8'hff && ywe) ##1 (!ywe && yaddr == 8'h00)
  );
endmodule

bind csconvert_mono csconvert_mono_sva mono_sva (
  .en(en), .clk(clk), .din(din), .pre_first_in(pre_first_in),
  .y_out(y_out), .yaddr(yaddr), .ywe(ywe), .pre_first_out(pre_first_out)
);

// ======================= csconvert_jp4 =======================
module csconvert_jp4_sva (
  input  logic        en,
  input  logic        clk,
  input  logic [7:0]  din,
  input  logic        pre_first_in,
  input  logic [7:0]  y_out,
  input  logic [7:0]  yaddr,
  input  logic        ywe,
  input  logic        pre_first_out,
  input  logic [7:0]  yaddr_cntr
);
  default clocking cb @(posedge clk); endclocking
  logic past_valid; always_ff @(posedge clk) past_valid <= 1'b1;

  // Combinational outputs
  assert property (y_out == {~din[7], din[6:0]});
  assert property (pre_first_out == pre_first_in);

  // Address mapping
  assert property (yaddr == {yaddr_cntr[4], yaddr_cntr[7:5], yaddr_cntr[0], yaddr_cntr[3:1]});

  // ywe next-state relation (uses mapped yaddr on previous cycle)
  assert property (disable iff(!past_valid)
    ywe == ($past(en) & ($past(pre_first_in) | ($past(ywe) & ($past(yaddr) != 8'hff))))
  );

  // yaddr_cntr next-state relation
  assert property (disable iff(!past_valid)
    (!$past(en) || $past(pre_first_in)) |-> (yaddr_cntr == 8'h00)
  );
  assert property (disable iff(!past_valid)
    ($past(en) && !$past(pre_first_in) && $past(ywe)) |-> (yaddr_cntr == $past(yaddr_cntr) + 8'h01)
  );
  assert property (disable iff(!past_valid)
    ($past(en) && !$past(pre_first_in) && !$past(ywe)) |-> (yaddr_cntr == $past(yaddr_cntr))
  );

  // Coverage: mapped address reaches 0xff and burst ends
  cover property (disable iff(!past_valid)
    en ##1 pre_first_in ##1 ywe [*1:$] ##0 (yaddr == 8'hff && ywe) ##1 (!ywe)
  );
endmodule

bind csconvert_jp4 csconvert_jp4_sva jp4_sva (
  .en(en), .clk(clk), .din(din), .pre_first_in(pre_first_in),
  .y_out(y_out), .yaddr(yaddr), .ywe(ywe), .pre_first_out(pre_first_out),
  .yaddr_cntr(yaddr_cntr)
);

// ======================= csconvert_jp4diff =======================
module csconvert_jp4diff_sva (
  input  logic        en,
  input  logic        clk,
  input  logic        scale_diff,
  input  logic        hdr,
  input  logic [7:0]  din,
  input  logic        pre_first_in,
  input  logic [8:0]  y_out,
  input  logic [7:0]  yaddr,
  input  logic        ywe,
  input  logic        pre_first_out,
  input  logic [1:0]  bayer_phase,

  // Internals we assert against
  input  logic        dly_1,
  input  logic [14:0] dly_16,
  input  logic        dly_17,
  input  logic        start_out,
  input  logic [7:0]  iadr,
  input  logic        iadr_run,
  input  logic [1:0]  mux_plus_sel,
  input  logic [2:0]  mux_minus_sel,
  input  logic        hdr_bit,
  input  logic [1:0]  scale_color,
  input  logic [1:0]  is_color,
  input  logic [7:0]  mux_plus,
  input  logic [7:0]  mux_minus,
  input  logic [7:0]  dd0,
  input  logic [7:0]  dd1,
  input  logic [7:0]  dd16,
  input  logic [7:0]  dd17,
  input  logic [14:0] ddsr0,ddsr1,ddsr2,ddsr3,ddsr4,ddsr5,ddsr6,ddsr7,
  input  logic [8:0]  pre_y_out,
  input  logic [7:0]  yaddr_cntr,
  input  logic [7:0]  pre_yaddr_cntr,
  input  logic [7:0]  pre2_yaddr_cntr,
  input  logic [2:0]  pre_ywe,
  input  logic [2:0]  pre2_first_out,
  input  logic [8:0]  scaled_pre_y_out
);
  default clocking cb @(posedge clk); endclocking
  logic past_valid; always_ff @(posedge clk) past_valid <= 1'b1;

  // Start alignment to pre_first_out (total delay depends on bayer_phase: 3/4/19/20)
  assert property (disable iff(!past_valid) (bayer_phase==2'b00) |-> pre_first_out == $past(pre_first_in, 3));
  assert property (disable iff(!past_valid) (bayer_phase==2'b01) |-> pre_first_out == $past(pre_first_in, 4));
  assert property (disable iff(!past_valid) (bayer_phase==2'b10) |-> pre_first_out == $past(pre_first_in, 19));
  assert property (disable iff(!past_valid) (bayer_phase==2'b11) |-> pre_first_out == $past(pre_first_in, 20));

  // start_out pipeline to pre_first_out
  assert property (disable iff(!past_valid) pre_first_out == $past(start_out,3));

  // Delay line correctness
  assert property (dly_1 == $past(pre_first_in));
  assert property (dly_16 == {$past(dly_16[13:0]), $past(dly_1)});
  assert property (dly_17 == $past(dly_16[14]));

  // iadr_run and iadr next-state relations
  assert property (disable iff(!past_valid)
    iadr_run == ($past(en) & ($past(start_out) | ($past(iadr_run) & ($past(iadr) != 8'hff))))
  );
  assert property (disable iff(!past_valid)
    (!$past(en) || $past(start_out)) |-> (iadr == 8'h00)
  );
  assert property (disable iff(!past_valid)
    ($past(en) && !$past(start_out) && $past(iadr_run)) |-> (iadr == $past(iadr) + 8'h01)
  );
  assert property (disable iff(!past_valid)
    ($past(en) && !$past(start_out) && !$past(iadr_run)) |-> (iadr == $past(iadr))
  );

  // ywe is 3-cycle delayed iadr_run
  assert property (disable iff(!past_valid) pre_ywe[0] == $past(iadr_run,1));
  assert property (disable iff(!past_valid) pre_ywe[1] == $past(iadr_run,2));
  assert property (disable iff(!past_valid) pre_ywe[2] == $past(iadr_run,3));
  assert property (disable iff(!past_valid) ywe == $past(iadr_run,3));

  // yaddr pipeline and mapping
  assert property (disable iff(!past_valid) pre2_yaddr_cntr == $past(iadr,1));
  assert property (disable iff(!past_valid) pre_yaddr_cntr  == $past(iadr,2));
  assert property (disable iff(!past_valid) yaddr_cntr      == $past(iadr,3));
  assert property (yaddr == {yaddr_cntr[4], yaddr_cntr[7:5], yaddr_cntr[0], yaddr_cntr[3:1]});

  // dd path and bit-serial shift arrays
  assert property (disable iff(!past_valid) dd0 == $past(din));
  assert property (disable iff(!past_valid) dd1 == $past(dd0));
  assert property (disable iff(!past_valid) ddsr0 == {$past(ddsr0[13:0]), $past(dd1[0])});
  assert property (disable iff(!past_valid) ddsr1 == {$past(ddsr1[13:0]), $past(dd1[1])});
  assert property (disable iff(!past_valid) ddsr2 == {$past(ddsr2[13:0]), $past(dd1[2])});
  assert property (disable iff(!past_valid) ddsr3 == {$past(ddsr3[13:0]), $past(dd1[3])});
  assert property (disable iff(!past_valid) ddsr4 == {$past(ddsr4[13:0]), $past(dd1[4])});
  assert property (disable iff(!past_valid) ddsr5 == {$past(ddsr5[13:0]), $past(dd1[5])});
  assert property (disable iff(!past_valid) ddsr6 == {$past(ddsr6[13:0]), $past(dd1[6])});
  assert property (disable iff(!past_valid) ddsr7 == {$past(ddsr7[13:0]), $past(dd1[7])});
  assert property (dd16 == {ddsr7[14],ddsr6[14],ddsr5[14],ddsr4[14],ddsr3[14],ddsr2[14],ddsr1[14],ddsr0[14]});
  assert property (disable iff(!past_valid) dd17 == $past(dd16));

  // Decode function for selector expectations
  function automatic logic [5:0] expected_sel (input logic [3:0] key);
    // returns {mux_plus_sel[1:0], mux_minus_sel[2:0], hdr_bit}
    case (key)
      4'b0000: expected_sel = {2'h0,3'h4,1'h0};
      4'b0001: expected_sel = {2'h0,3'h1,1'h0};
      4'b0010: expected_sel = {2'h0,3'h2,1'h0};
      4'b0011: expected_sel = {2'h0,3'h3,1'h1};
      4'b0100: expected_sel = {2'h1,3'h0,1'h0};
      4'b0101: expected_sel = {2'h1,3'h4,1'h0};
      4'b0110: expected_sel = {2'h1,3'h2,1'h1};
      4'b0111: expected_sel = {2'h1,3'h3,1'h0};
      4'b1000: expected_sel = {2'h2,3'h0,1'h0};
      4'b1001: expected_sel = {2'h2,3'h1,1'h1};
      4'b1010: expected_sel = {2'h2,3'h4,1'h0};
      4'b1011: expected_sel = {2'h2,3'h3,1'h0};
      4'b1100: expected_sel = {2'h3,3'h0,1'h1};
      4'b1101: expected_sel = {2'h3,3'h1,1'h0};
      4'b1110: expected_sel = {2'h3,3'h2,1'h0};
      4'b1111: expected_sel = {2'h3,3'h4,1'h0};
      default: expected_sel = '0;
    endcase
  endfunction

  // Selector decode must match expected from previous iadr/bayer_phase (NB semantics)
  assert property (disable iff(!past_valid)
    {mux_plus_sel, mux_minus_sel, hdr_bit} == expected_sel({$past(bayer_phase), $past(iadr[4]), $past(iadr[0])})
  );

  // When not updating, mux outputs hold
  assert property (disable iff(!past_valid)
    !$past(pre_ywe[0]) |-> ($stable(mux_plus) && $stable(mux_minus))
  );

  // When updating, mux_plus selects the correct prior dd source
  assert property (disable iff(!past_valid)
    $past(pre_ywe[0]) |->
      ( ($past(mux_plus_sel)==2'h0 && mux_plus==$past(dd0)) ||
        ($past(mux_plus_sel)==2'h1 && mux_plus==$past(dd1)) ||
        ($past(mux_plus_sel)==2'h2 && mux_plus==$past(dd16))||
        ($past(mux_plus_sel)==2'h3 && mux_plus==$past(dd17)) )
  );

  // When updating, mux_minus selects ddX or zeros with HDR override
  assert property (disable iff(!past_valid)
    $past(pre_ywe[0]) |->
      ( (($past(mux_minus_sel[2]) | ($past(hdr_bit) & $past(hdr)))) ? (mux_minus==8'h00) :
        ( (($past(mux_minus_sel[1:0])==2'h0) && mux_minus==$past(dd0))  ||
          (($past(mux_minus_sel[1:0])==2'h1) && mux_minus==$past(dd1))  ||
          (($past(mux_minus_sel[1:0])==2'h2) && mux_minus==$past(dd16)) ||
          (($past(mux_minus_sel[1:0])==2'h3) && mux_minus==$past(dd17)) ) )
  );

  // is_color and scale_color shift/update
  assert property (disable iff(!past_valid)
    is_color[1] == $past(is_color[0]) &&
    is_color[0] == ~($past(mux_minus_sel[2]) | ($past(hdr_bit) & $past(hdr)))
  );
  assert property (disable iff(!past_valid)
    scale_color[1] == $past(scale_color[0]) &&
    scale_color[0] == (~($past(mux_minus_sel[2]) | ($past(hdr_bit) & $past(hdr))) & $past(scale_diff))
  );

  // pre_y_out update on pre_ywe[1]
  assert property (disable iff(!past_valid)
    $past(pre_ywe[1]) |-> (pre_y_out == ({1'b0,$past(mux_plus)} - {1'b0,$past(mux_minus)}))
  );
  assert property (disable iff(!past_valid)
    !$past(pre_ywe[1]) |-> $stable(pre_y_out)
  );

  // scaled_pre_y_out combinational correctness
  assert property (scaled_pre_y_out == (scale_color[1] ? {pre_y_out[8], pre_y_out[8:1]} : pre_y_out));

  // y_out next-state from prior scaled_pre_y_out and is_color
  assert property (disable iff(!past_valid)
    y_out == ($past(scale_color[1]) ? { $past(pre_y_out[8]), $past(pre_y_out[8:1]) } : $past(pre_y_out)) - {1'b0, ~$past(is_color[1]), 7'h00}
  );

  // Coverage: run through a full burst and exercise HDR zeroing and scaling
  cover property (disable iff(!past_valid)
    en ##1 pre_first_out ##1 ywe [*10:$] ##1 (yaddr == 8'hff && ywe) ##1 !ywe
  );
  cover property (disable iff(!past_valid)
    $past(pre_ywe[0]) && ($past(mux_minus_sel[2]) | ($past(hdr_bit) & $past(hdr))) && (mux_minus==8'h00)
  );
  cover property (disable iff(!past_valid)
    $past(pre_ywe[1]) && $past(scale_color[1])
  );
endmodule

bind csconvert_jp4diff csconvert_jp4diff_sva jp4diff_sva (
  .en(en), .clk(clk), .scale_diff(scale_diff), .hdr(hdr), .din(din), .pre_first_in(pre_first_in),
  .y_out(y_out), .yaddr(yaddr), .ywe(ywe), .pre_first_out(pre_first_out), .bayer_phase(bayer_phase),
  .dly_1(dly_1), .dly_16(dly_16), .dly_17(dly_17), .start_out(start_out),
  .iadr(iadr), .iadr_run(iadr_run), .mux_plus_sel(mux_plus_sel), .mux_minus_sel(mux_minus_sel),
  .hdr_bit(hdr_bit), .scale_color(scale_color), .is_color(is_color),
  .mux_plus(mux_plus), .mux_minus(mux_minus), .dd0(dd0), .dd1(dd1), .dd16(dd16), .dd17(dd17),
  .ddsr0(ddsr0), .ddsr1(ddsr1), .ddsr2(ddsr2), .ddsr3(ddsr3), .ddsr4(ddsr4), .ddsr5(ddsr5), .ddsr6(ddsr6), .ddsr7(ddsr7),
  .pre_y_out(pre_y_out), .yaddr_cntr(yaddr_cntr), .pre_yaddr_cntr(pre_yaddr_cntr), .pre2_yaddr_cntr(pre2_yaddr_cntr),
  .pre_ywe(pre_ywe), .pre2_first_out(pre2_first_out), .scaled_pre_y_out(scaled_pre_y_out)
);