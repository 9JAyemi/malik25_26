// SVA checker for sync_w2r
module sync_w2r_sva #(parameter ASIZE=4) (
  input  logic              rclk,
  input  logic              rrst_n,
  input  logic [ASIZE:0]    wptr,
  input  logic [ASIZE:0]    rq1_wptr, // internal flop
  input  logic [ASIZE:0]    rq2_wptr  // output flop
);

  default clocking cb @(posedge rclk); endclocking
  default disable iff (!rrst_n);

  // Asynchronous reset immediately clears both flops
  assert property (@(negedge rrst_n) (rq1_wptr=='0 && rq2_wptr=='0));
  // Hold zeros while in reset
  assert property (!rrst_n |-> (rq1_wptr=='0 && rq2_wptr=='0));
  // On first active clock after reset release, rq2_wptr is still 0 (pipeline bubble)
  assert property ( rrst_n && !$past(rrst_n) |-> rq2_wptr=='0 );

  // 2-flop pipeline transfer
  assert property ( {rq2_wptr, rq1_wptr} == $past({rq1_wptr, wptr}) );

  // Direct 2-cycle relation to input once out of reset for 2 cycles
  assert property ( rrst_n && $past(rrst_n) && $past(rrst_n,2) |-> rq2_wptr == $past(wptr,2) );

  // No X/Z on synchronizer flops when out of reset
  assert property ( !$isunknown(rq1_wptr) && !$isunknown(rq2_wptr) );

  // Captured pointer should progress in Gray code (0 or 1 bit change per cycle)
  assert property ( $past(rrst_n) |-> $onehot0(rq2_wptr ^ $past(rq2_wptr)) );

  // Coverage
  cover property (! $past(rrst_n) && rrst_n);                                // reset release
  cover property ( $changed(rq2_wptr) );                                      // any change seen
  cover property ( $changed(wptr) ##1 (rq1_wptr==$past(wptr)) ##1 (rq2_wptr==$past(wptr,2)) );

  genvar i;
  for (i=0; i<=ASIZE; i++) begin : cg_bits
    cover property ( $rose(rq2_wptr[i]) );
    cover property ( $fell(rq2_wptr[i]) );
  end

endmodule

// Bind into the DUT (allows access to internal rq1_wptr)
bind sync_w2r sync_w2r_sva #(.ASIZE(ASIZE)) u_sync_w2r_sva (
  .rclk    (rclk),
  .rrst_n  (rrst_n),
  .wptr    (wptr),
  .rq1_wptr(rq1_wptr),
  .rq2_wptr(rq2_wptr)
);