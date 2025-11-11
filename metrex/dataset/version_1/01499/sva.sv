// SVA for jt10_adpcm_acc
// Bind into the DUT to check key behaviors, arithmetic, gating, and output saturation.
// Focused, concise, and high-value checks with basic functional coverage.

bind jt10_adpcm_acc jt10_adpcm_acc_sva();

module jt10_adpcm_acc_sva;

  // Clocking and reset
  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Helper functions
  function automatic signed [17:0] sx18(input signed [15:0] a);
    return { {2{a[15]}}, a };
  endfunction
  function automatic signed [22:0] sx23_18(input signed [17:0] a);
    return { {5{a[17]}}, a };
  endfunction

  // Basic signal definitions correctness
  assert property (adv == (en_ch[0] & cur_ch[0]));
  assert property (overflow == (|pcm_full[17:15] & ~&pcm_full[17:15]));
  assert property (en_sum |-> pcm_in_long == sx18(pcm_in));
  assert property (!en_sum |-> pcm_in_long == 18'sd0);

  // Reset values (regs cleared)
  assert property (!rst_n |=> (acc==18'sd0 && last==18'sd0 && step==18'sd0 && pcm_full==18'sd0));

  // Combinational arithmetic correctness (sanity of internal math)
  assert property (diff == acc - last);
  assert property (diff_ext == sx23_18(diff));
  assert property (step_full == (diff_ext + (diff_ext<<1) + (diff_ext<<3) + (diff_ext<<5)));

  // acc update semantics
  assert property (cen && match &&  cur_ch[0] |=> acc == $past(pcm_in_long));
  assert property (cen && match && !cur_ch[0] |=> acc == $past(pcm_in_long + acc));
  assert property (!(cen && match) |=> acc == $past(acc));

  // last update semantics (captures old acc when adv)
  assert property (cen && adv |=> last == $past(acc));
  assert property (!(cen && adv) |=> last == $past(last));

  // step update semantics (from prior step_full)
  assert property (cen && adv |=> step == { {2{$past(step_full[22])}}, $past(step_full[22:7]) });
  assert property (!(cen && adv) |=> step == $past(step));

  // pcm_full update semantics
  assert property (cen && cur_ch[0] && en_ch == 6'b000001 |=> pcm_full == $past(last));
  assert property (cen && cur_ch[0] && (en_ch == 6'b000100 || en_ch == 6'b010000)
                   |=> pcm_full == $past(pcm_full + step));
  assert property (cen && cur_ch[0] && !(en_ch inside {6'b000001,6'b000100,6'b010000})
                   |=> pcm_full == $past(pcm_full));
  assert property (!(cen && cur_ch[0]) |=> pcm_full == $past(pcm_full));

  // pcm_out update and saturation behavior
  // Note: pcm_out is based on prior-cycle overflow/pcm_full
  assert property (cen && cur_ch[0] &&  $past(overflow) &&  $past(pcm_full[17]) |=> pcm_out == 16'h8000);
  assert property (cen && cur_ch[0] &&  $past(overflow) && !$past(pcm_full[17]) |=> pcm_out == 16'h7fff);
  assert property (cen && cur_ch[0] && !$past(overflow) |=> pcm_out == $past(pcm_full[15:0]));
  assert property (!(cen && cur_ch[0]) |=> pcm_out == $past(pcm_out));

  // X/Z checks on key outputs/regs when updated
  assert property (cen && cur_ch[0] |-> !$isunknown({overflow, pcm_full, pcm_out}));
  assert property (cen && (match || adv) |-> !$isunknown({acc, last, step}));

  // Functional coverage (concise, key scenarios)
  cover property (cen && match &&  cur_ch[0]);               // acc load path
  cover property (cen && match && !cur_ch[0]);               // acc accumulate path
  cover property (cen && adv);                                // last/step update
  cover property (cen && cur_ch[0] && en_ch == 6'b000001);    // pcm_full = last
  cover property (cen && cur_ch[0] && en_ch == 6'b000100);    // pcm_full += step (case 1)
  cover property (cen && cur_ch[0] && en_ch == 6'b010000);    // pcm_full += step (case 2)
  cover property (cen && cur_ch[0] && $past(overflow) &&  $past(pcm_full[17]));  // neg saturation
  cover property (cen && cur_ch[0] && $past(overflow) && !$past(pcm_full[17]));  // pos saturation
  cover property (cen && cur_ch[0] && !$past(overflow));      // no saturation
  cover property ($rose(en_sum));                              // exercise pcm_in_long gating

endmodule