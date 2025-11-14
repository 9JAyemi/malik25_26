// SVA binders for cdc_syncfifo and submodules.
// Focus: pointer math, Gray-code behavior, flag correctness, CDC sync, and protocol misuse.
// Concise, high-signal-importance coverage included.

////////////////////////////////////////////////////////////
// wptr_full assertions (write domain)
module wptr_full_sva #(parameter ADDRSIZE=2) ();
  localparam int DEPTH = 1<<ADDRSIZE;

  default clocking cb @(posedge wclk); endclocking
  default disable iff (wrst);

  // Reset outcome
  assert property (@cb wrst |=> (wbin==0 && wptr==0 && wfull==0));

  // Binary pointer update equation
  assert property (@cb wbin == $past(wbin) + ($past(winc) & ~$past(wfull)));

  // Gray code: one-bit toggle on increment, stable otherwise
  assert property (@cb $past(winc & ~wfull) |-> $onehot(wptr ^ $past(wptr)));
  assert property (@cb !$past(winc & ~wfull) |-> (wptr == $past(wptr)));

  // Address mapping
  assert property (@cb waddr == wbin[ADDRSIZE-1:0]);

  // Full flag correctness
  assert property (@cb wfull == wfull_val);

  // Protocol: no write when full
  assert property (@cb !(winc && wfull));

  // Coverage: fill to full, drop full, wrap (MSB toggles)
  cover property (@cb (winc && ~wfull)[*DEPTH] ##1 wfull);
  cover property (@cb $fell(wfull));
  cover property (@cb $changed(wptr[ADDRSIZE]));
endmodule

bind wptr_full wptr_full_sva #(.ADDRSIZE(ADDRSIZE)) wptr_full_sva_i();

////////////////////////////////////////////////////////////
// rptr_empty assertions (read domain)
module rptr_empty_sva #(parameter ADDRSIZE=2) ();
  localparam int DEPTH = 1<<ADDRSIZE;

  default clocking cb @(posedge rclk); endclocking
  default disable iff (rrst);

  // Reset outcome
  assert property (@cb rrst |=> (rbin==0 && rptr==0 && rempty==1));

  // Binary pointer update equation
  assert property (@cb rbin == $past(rbin) + ($past(rinc) & ~$past(rempty)));

  // Gray code: one-bit toggle on increment, stable otherwise
  assert property (@cb $past(rinc & ~rempty) |-> $onehot(rptr ^ $past(rptr)));
  assert property (@cb !$past(rinc & ~rempty) |-> (rptr == $past(rptr)));

  // Address mapping
  assert property (@cb raddr == rbin[ADDRSIZE-1:0]);

  // Empty flag correctness
  assert property (@cb rempty == rempty_val);

  // Protocol: no read when empty
  assert property (@cb !(rinc && rempty));

  // Coverage: drain to empty, empty deassert/reassert, wrap (MSB toggles)
  cover property (@cb (rinc && ~rempty)[*DEPTH] ##1 rempty);
  cover property (@cb $rose(rempty));
  cover property (@cb $changed(rptr[ADDRSIZE]));
endmodule

bind rptr_empty rptr_empty_sva #(.ADDRSIZE(ADDRSIZE)) rptr_empty_sva_i();

////////////////////////////////////////////////////////////
// CDC synchronizer assertions (r->w domain)
module cdc_sync_r2w_sva #(parameter ADDRSIZE=2) ();
  default clocking cb @(posedge wclk); endclocking
  default disable iff (wrst);

  // Two-flop pipeline behavior and reset outcome
  assert property (@cb wrst |=> (wq2_rptr==0 && cdc_sync_wq1_rptr==0));
  assert property (@cb wq2_rptr == $past(cdc_sync_wq1_rptr));
  assert property (@cb cdc_sync_wq1_rptr == $past(rptr));

  // Coverage: synchronized pointer changes observed
  cover property (@cb $changed(wq2_rptr));
endmodule

bind cdc_sync_r2w cdc_sync_r2w_sva #(.ADDRSIZE(ADDRSIZE)) cdc_sync_r2w_sva_i();

////////////////////////////////////////////////////////////
// CDC synchronizer assertions (w->r domain)
module cdc_sync_w2r_sva #(parameter ADDRSIZE=2) ();
  default clocking cb @(posedge rclk); endclocking
  default disable iff (rrst);

  // Two-flop pipeline behavior and reset outcome
  assert property (@cb rrst |=> (rq2_wptr==0 && cdc_sync_rq1_wptr==0));
  assert property (@cb rq2_wptr == $past(cdc_sync_rq1_wptr));
  assert property (@cb cdc_sync_rq1_wptr == $past(wptr));

  // Coverage: synchronized pointer changes observed
  cover property (@cb $changed(rq2_wptr));
endmodule

bind cdc_sync_w2r cdc_sync_w2r_sva #(.ADDRSIZE(ADDRSIZE)) cdc_sync_w2r_sva_i();

////////////////////////////////////////////////////////////
// Memory port assertions (write-port protocol only)
module cdc_fifomem_sva #(parameter DATASIZE=34, parameter ADDRSIZE=2) ();
  default clocking cb @(posedge wclk); endclocking

  // Protocol: design must not be asked to write when full
  assert property (@cb !(wclken && wfull));

  // Coverage: successful write occurrences
  cover property (@cb wclken && !wfull);
endmodule

bind cdc_fifomem cdc_fifomem_sva #(.DATASIZE(DATASIZE), .ADDRSIZE(ADDRSIZE)) cdc_fifomem_sva_i();