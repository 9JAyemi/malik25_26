// SVA for cdc_pulse_sync
// Concise checks for pulse transfer, handshake, CDC latency and one-shot behavior.
// Bind this module to the DUT to verify internal regs.

module cdc_pulse_sync_sva #(
  parameter int unsigned MAX_IN2OUT = 64,  // upper bound for req->pulse latency
  parameter int unsigned MAX_ACK    = 64   // upper bound for ack return latency
)(
  input  logic         clk_in,
  input  logic         clk_out,
  input  logic         pulse_in,
  input  logic         pulse_out,
  input  logic  [1:0]  in_pre_sync,
  input  logic         in_sync_pulse,
  input  logic  [2:0]  out_sync,
  input  logic  [1:0]  aq_sync_ff,
  input  logic         aq_sync
);

  // Past-valid guards to avoid time-0 artifacts
  bit in_pv, out_pv;
  always @(posedge clk_in)  in_pv  <= 1'b1;
  always @(posedge clk_out) out_pv <= 1'b1;

  // ----------------------------------------------------------------------------
  // Structural pipeline checks (sanity)
  // ----------------------------------------------------------------------------
  // clk_in domain sync-stage behavior
  assert property (@(posedge clk_in) disable iff (!in_pv)
                   in_pre_sync[1] == $past(in_pre_sync[0]))
    else $error("in_pre_sync[1] must equal prior in_pre_sync[0]");

  // clk_out domain sync-stage behavior
  assert property (@(posedge clk_out) disable iff (!out_pv)
                   out_sync[1] == $past(out_sync[0]))
    else $error("out_sync[1] must equal prior out_sync[0]");
  assert property (@(posedge clk_out) disable iff (!out_pv)
                   out_sync[2] == $past(out_sync[1]))
    else $error("out_sync[2] must equal prior out_sync[1]");

  // ack sync-back behavior (two-stage)
  assert property (@(posedge clk_in) disable iff (!in_pv)
                   aq_sync == aq_sync_ff[1])
    else $error("aq_sync must equal aq_sync_ff[1]");

  // ----------------------------------------------------------------------------
  // in_sync_pulse generation and handshake discipline (clk_in)
  // ----------------------------------------------------------------------------
  // Set only on detected rising edge in in_pre_sync and when not acked
  assert property (@(posedge clk_in) disable iff (!in_pv)
                   (!aq_sync && !in_sync_pulse && !in_pre_sync[1] && in_pre_sync[0]) |=> in_sync_pulse)
    else $error("in_sync_pulse must set on edge detect when not acked");

  // Clear on ack next cycle
  assert property (@(posedge clk_in) disable iff (!in_pv)
                   aq_sync |=> !in_sync_pulse)
    else $error("in_sync_pulse must clear on aq_sync");

  // Hold high until ack arrives
  assert property (@(posedge clk_in) disable iff (!in_pv)
                   in_sync_pulse && !aq_sync |=> in_sync_pulse)
    else $error("in_sync_pulse must hold until ack");

  // No second rise while already high
  assert property (@(posedge clk_in) disable iff (!in_pv)
                   in_sync_pulse |-> ! $rose(in_sync_pulse))
    else $error("in_sync_pulse cannot re-rise while high");

  // ----------------------------------------------------------------------------
  // pulse_out one-shot and safety (clk_out)
  // ----------------------------------------------------------------------------
  // pulse_out is one cycle only
  assert property (@(posedge clk_out) disable iff (!out_pv)
                   pulse_out |=> !pulse_out)
    else $error("pulse_out must be single-cycle");

  // pulse_out can only occur when there is a pending request (in_sync_pulse high)
  assert property (@(posedge clk_out) disable iff (!out_pv)
                   pulse_out |-> in_sync_pulse)
    else $error("pulse_out without pending request");

  // ----------------------------------------------------------------------------
  // Cross-domain liveness and ordering (bounded fairness)
  // ----------------------------------------------------------------------------
  // Each request causes a pulse_out within MAX_IN2OUT clk_out cycles
  assert property (@(posedge clk_in) disable iff (!in_pv)
                   $rose(in_sync_pulse) |-> ##[0:MAX_IN2OUT] @(posedge clk_out) $rose(pulse_out))
    else $error("Missing/late pulse_out for request");

  // When out_sync[2] rises (sink sees request), aq_sync returns within MAX_ACK clk_in cycles
  assert property (@(posedge clk_out) disable iff (!out_pv)
                   $rose(out_sync[2]) |-> ##[0:MAX_ACK] @(posedge clk_in) aq_sync)
    else $error("Missing/late aq_sync return");

  // While request is pending, sink-side level out_sync[2] must eventually assert and remain until clear
  assert property (@(posedge clk_out) disable iff (!out_pv)
                   in_sync_pulse |-> ##[0:MAX_IN2OUT] out_sync[2])
    else $error("out_sync[2] did not assert while request pending");
  assert property (@(posedge clk_out) disable iff (!out_pv)
                   (out_sync[2] && in_sync_pulse) |=> out_sync[2])
    else $error("out_sync[2] must stay high while request pending");

  // Ack implies sink-side level is high (since request still pending when ack observed)
  assert property (@(posedge clk_in) disable iff (!in_pv)
                   aq_sync |-> out_sync[2])
    else $error("aq_sync high while out_sync[2] low");

  // After request clears in source, sink level drops within MAX_IN2OUT clk_out cycles
  assert property (@(posedge clk_in) disable iff (!in_pv)
                   $fell(in_sync_pulse) |-> ##[0:MAX_IN2OUT] @(posedge clk_out) $fell(out_sync[2]))
    else $error("out_sync[2] did not deassert after request cleared");

  // ----------------------------------------------------------------------------
  // Coverage: full handshake cycle
  // ----------------------------------------------------------------------------
  cover property (
    @(posedge clk_in) disable iff (!in_pv)
      $rose(in_sync_pulse)
      ##[0:MAX_IN2OUT] @(posedge clk_out) $rose(pulse_out)
      ##[0:MAX_ACK]    @(posedge clk_in)  aq_sync
      ##1                                  !in_sync_pulse
      ##[0:MAX_IN2OUT] @(posedge clk_out) $fell(out_sync[2])
      ##[0:MAX_ACK]    @(posedge clk_in)  !aq_sync
  );

endmodule

// Bind into the DUT (connect internal regs for white-box checks)
bind cdc_pulse_sync cdc_pulse_sync_sva #(
  .MAX_IN2OUT(64),
  .MAX_ACK(64)
) cdc_pulse_sync_sva_i (
  .clk_in      (clk_in),
  .clk_out     (clk_out),
  .pulse_in    (pulse_in),
  .pulse_out   (pulse_out),
  .in_pre_sync (in_pre_sync),
  .in_sync_pulse(in_sync_pulse),
  .out_sync    (out_sync),
  .aq_sync_ff  (aq_sync_ff),
  .aq_sync     (aq_sync)
);