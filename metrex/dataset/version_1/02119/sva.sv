// Bind these assertions to mc_crt
bind mc_crt mc_crt_sva mc_crt_sva_i();

module mc_crt_sva;

  // Shorthands
  let req_t_m = (req_sync_2 ^ req_sync_3);
  let gnt_t_p = (gnt_sync_2 ^ gnt_sync_3);
  let full    = requests[1];

  // Reset values
  assert property (@(posedge pixclk) !reset_n |-> (crt_ready && !capt_req &&
                          capt_org==21'h0 && capt_ptch==12'h0 && capt_x==10'h0 && capt_y==12'h0 &&
                          capt_page==5'h0 && !gnt_sync_1 && !gnt_sync_2 && !gnt_sync_3));

  assert property (@(posedge mclock) !reset_n |-> (!crt_arb_req && !final_grant &&
                          requests==2'b00 && !hold_req && pmult==21'h0 && int_add==21'h0 &&
                          !req_sync_m1 && !req_sync_1 && !req_sync_2 && !req_sync_3 &&
                          crt_arb_page==5'h0 && crt_arb_addr==21'h0));

  // Pixel-domain request protocol and capture
  assert property (@(posedge pixclk) disable iff (!reset_n)
                   (crt_req && crt_clock) |-> $past(crt_ready));

  assert property (@(posedge pixclk) disable iff (!reset_n)
                   (crt_req && crt_clock) |=> (capt_req == !$past(capt_req) &&
                                               capt_org  == $past(crt_org)  &&
                                               capt_ptch == $past(crt_ptch) &&
                                               capt_x    == $past(crt_x)    &&
                                               capt_y    == $past(crt_y)    &&
                                               capt_page == ($past(crt_page) - 5'd1) &&
                                               !crt_ready));

  // No-op if crt_req asserted when crt_clock is low
  assert property (@(posedge pixclk) disable iff (!reset_n)
                   (crt_req && !crt_clock) |=> (capt_req == $past(capt_req) &&
                                                $stable({capt_org,capt_ptch,capt_x,capt_y,capt_page}) &&
                                                $stable(crt_ready)));

  // Grant toggle pulse in pixclk and ready behavior
  assert property (@(posedge pixclk) disable iff (!reset_n) gnt_t_p |=> !gnt_t_p);
  assert property (@(posedge pixclk) disable iff (!reset_n) $rose(crt_ready) |-> gnt_t_p);
  assert property (@(posedge pixclk) disable iff (!reset_n)
                   (crt_req && crt_clock) |-> (!crt_ready until gnt_t_p));

  // Request toggle pulse in mclock
  assert property (@(posedge mclock) disable iff (!reset_n) req_t_m |=> !req_t_m);

  // final_grant toggles exactly with crt_gnt
  assert property (@(posedge mclock) disable iff (!reset_n) $changed(final_grant) |-> crt_gnt);
  assert property (@(posedge mclock) disable iff (!reset_n) crt_gnt |-> $changed(final_grant));

  // Arb req generation and handshake
  assert property (@(posedge mclock) disable iff (!reset_n) crt_gnt |-> !crt_arb_req);
  assert property (@(posedge mclock) disable iff (!reset_n) $rose(crt_arb_req) |-> (crt_arb_req until_with crt_gnt));
  assert property (@(posedge mclock) disable iff (!reset_n) crt_arb_req |-> !full);
  assert property (@(posedge mclock) disable iff (!reset_n)
                   $rose(crt_arb_req) |-> (!full && (req_t_m || hold_req)));

  // Payload correctness and stability while waiting for grant
  assert property (@(posedge mclock) disable iff (!reset_n)
                   $rose(crt_arb_req) |-> (crt_arb_page == capt_page &&
                                           crt_arb_addr == (pmult + int_add)));
  assert property (@(posedge mclock) disable iff (!reset_n)
                   (crt_arb_req && !crt_gnt) |=> ($stable(crt_arb_page) && $stable(crt_arb_addr)));

  // Hold logic
  assert property (@(posedge mclock) disable iff (!reset_n)
                   (req_t_m && full) |=> hold_req);
  assert property (@(posedge mclock) disable iff (!reset_n)
                   (hold_req && !full) |=> (!hold_req && crt_arb_req));

  // Requests counter behavior
  assert property (@(posedge mclock) disable iff (!reset_n)
                   ({crt_gnt,req_t_m}==2'b01) |=> (requests == $past(requests)+2'b01));
  assert property (@(posedge mclock) disable iff (!reset_n)
                   ({crt_gnt,req_t_m}==2'b10) |=> (requests == $past(requests)-2'b01));
  assert property (@(posedge mclock) disable iff (!reset_n)
                   ({crt_gnt,req_t_m} inside {2'b00,2'b11}) |=> (requests == $past(requests)));

  // CDC coverage (eventual propagation across domains)
  cover property (@(posedge pixclk) disable iff (!reset_n)
                  $changed(capt_req) |-> s_eventually @(posedge mclock) req_t_m);
  cover property (@(posedge mclock) disable iff (!reset_n)
                  $changed(final_grant) |-> s_eventually @(posedge pixclk) gnt_t_p);

  // End-to-end handshake coverage
  cover property (@(posedge pixclk) disable iff (!reset_n)
                  (crt_ready && crt_clock && crt_req)
                  ##0 s_eventually @(posedge mclock) $rose(crt_arb_req)
                  ##0 s_eventually @(posedge mclock) crt_gnt
                  ##0 s_eventually @(posedge pixclk) $rose(crt_ready));

  // Backpressure/release coverage
  cover property (@(posedge mclock) disable iff (!reset_n)
                  (full && req_t_m) ##1 hold_req ##[1:$] (!full) ##1 $rose(crt_arb_req) ##[1:$] crt_gnt);

endmodule