// SVA for tmu2_split: bind into DUT scope, no TB code required.

module tmu2_split_sva #(parameter cache_depth=13, fml_depth=26) ();

  default clocking cb @(posedge sys_clk); endclocking
  default disable iff (sys_rst);

  // Shorthands
  let any_miss  = (miss_a | miss_b | miss_c | miss_d);
  let both_acks = (frag_pipe_ack_i & fetch_pipe_ack_i);

  // Combinational definitions
  a_busy_def: assert property (busy == (frag_pipe_stb_o | fetch_pipe_stb_o));
  a_ack_def:  assert property (pipe_ack_o == ((~frag_pipe_stb_o & ~fetch_pipe_stb_o) | both_acks));

  // Ack/backpressure relationships
  a_ack_when_idle: assert property (!busy |-> pipe_ack_o);
  a_no_ack_when_busy: assert property ((busy && !both_acks) |-> !pipe_ack_o);

  // Strobe setting on pipe_ack_o (next-cycle effect of nonblocking assignments)
  a_load_on_ack: assert property (
    pipe_ack_o |=> (
      // stbs
      (frag_pipe_stb_o == $past(pipe_stb_i)) &&
      (fetch_pipe_stb_o == ($past(pipe_stb_i) & $past(any_miss))) &&
      // captured/scattered payloads
      (frag_dadr   == $past(dadr)) &&
      (frag_x_frac == $past(x_frac)) &&
      (frag_y_frac == $past(y_frac)) &&
      (frag_miss_a == $past(miss_a)) &&
      (frag_miss_b == $past(miss_b)) &&
      (frag_miss_c == $past(miss_c)) &&
      (frag_miss_d == $past(miss_d)) &&
      (fetch_miss_a == $past(miss_a)) &&
      (fetch_miss_b == $past(miss_b)) &&
      (fetch_miss_c == $past(miss_c)) &&
      (fetch_miss_d == $past(miss_d)) &&
      (frag_tadra == $past(tadra[cache_depth-1:0])) &&
      (frag_tadrb == $past(tadrb[cache_depth-1:0])) &&
      (frag_tadrc == $past(tadrc[cache_depth-1:0])) &&
      (frag_tadrd == $past(tadrd[cache_depth-1:0])) &&
      (fetch_tadra == $past(tadra[fml_depth-1:5])) &&
      (fetch_tadrb == $past(tadrb[fml_depth-1:5])) &&
      (fetch_tadrc == $past(tadrc[fml_depth-1:5])) &&
      (fetch_tadrd == $past(tadrd[fml_depth-1:5]))
    )
  );

  // Strobe clear when ack only (no new load)
  a_frag_clear_on_ack_only:  assert property (frag_pipe_ack_i && !pipe_ack_o |=> !frag_pipe_stb_o);
  a_fetch_clear_on_ack_only: assert property (fetch_pipe_ack_i && !pipe_ack_o |=> !fetch_pipe_stb_o);

  // Strobe hold when no ack and no new load
  a_frag_hold:  assert property (!frag_pipe_ack_i && !pipe_ack_o |=> $stable(frag_pipe_stb_o));
  a_fetch_hold: assert property (!fetch_pipe_ack_i && !pipe_ack_o |=> $stable(fetch_pipe_stb_o));

  // Strobes only rise due to pipe_ack_o
  a_frag_stb_rise_cause:  assert property ($rose(frag_pipe_stb_o)  |-> $past(pipe_ack_o && pipe_stb_i));
  a_fetch_stb_rise_cause: assert property ($rose(fetch_pipe_stb_o) |-> $past(pipe_ack_o && pipe_stb_i && any_miss));

  // No-miss implies no fetch strobe after load
  a_no_fetch_when_no_miss: assert property (pipe_ack_o && pipe_stb_i && !any_miss |=> !fetch_pipe_stb_o);

  // Miss outputs coherent across paths
  a_miss_coherent_a: assert property (frag_miss_a == fetch_miss_a);
  a_miss_coherent_b: assert property (frag_miss_b == fetch_miss_b);
  a_miss_coherent_c: assert property (frag_miss_c == fetch_miss_c);
  a_miss_coherent_d: assert property (frag_miss_d == fetch_miss_d);

  // Payload stability while busy without new load
  a_payload_stable_while_busy: assert property (
    ( (frag_pipe_stb_o || fetch_pipe_stb_o) && !pipe_ack_o ) |=> $stable({
      frag_dadr, frag_x_frac, frag_y_frac,
      frag_tadra, frag_tadrb, frag_tadrc, frag_tadrd,
      fetch_tadra, fetch_tadrb, fetch_tadrc, fetch_tadrd,
      frag_miss_a, frag_miss_b, frag_miss_c, frag_miss_d,
      fetch_miss_a, fetch_miss_b, fetch_miss_c, fetch_miss_d
    })
  );

  // Basic X-checks on controls after reset release
  a_ctrl_known: assert property (!$isunknown({frag_pipe_stb_o, fetch_pipe_stb_o, busy, pipe_ack_o}));

  // Coverage
  c_no_miss_txn:   cover property (pipe_ack_o && pipe_stb_i && !any_miss);
  c_miss_txn:      cover property (pipe_ack_o && pipe_stb_i &&  any_miss);
  c_back2back:     cover property ( (frag_pipe_stb_o || fetch_pipe_stb_o)
                                    ##1 (both_acks && pipe_stb_i)
                                    ##1 (frag_pipe_stb_o || fetch_pipe_stb_o) );
  c_ack_skew_f_then_fetch: cover property ( (frag_pipe_stb_o && fetch_pipe_stb_o)
                                            ##1 (frag_pipe_ack_i && !fetch_pipe_ack_i)
                                            ##[1:8] fetch_pipe_ack_i );
  c_ack_skew_fetch_then_f: cover property ( (frag_pipe_stb_o && fetch_pipe_stb_o)
                                            ##1 (!frag_pipe_ack_i && fetch_pipe_ack_i)
                                            ##[1:8] frag_pipe_ack_i );
  c_busy_drop: cover property (busy ##[1:10] !busy);

endmodule

bind tmu2_split tmu2_split_sva #(.cache_depth(cache_depth), .fml_depth(fml_depth)) sva_i();