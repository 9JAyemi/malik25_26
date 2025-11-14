// SVA for eproto_tx — concise, high-signal-coverage checks and targeted covers

module eproto_tx_sva (
  input  logic        txlclk_p,
  input  logic        reset,

  input  logic        emtx_access,
  input  logic        emtx_write,
  input  logic [1:0]  emtx_datamode,
  input  logic [3:0]  emtx_ctrlmode,
  input  logic [31:0] emtx_dstaddr,
  input  logic [31:0] emtx_srcaddr,
  input  logic [31:0] emtx_data,

  input  logic        tx_rd_wait,
  input  logic        tx_wr_wait,

  input  logic        emtx_ack,
  input  logic [7:0]  txframe_p,
  input  logic [63:0] txdata_p,

  input  logic        emtx_rd_wait,
  input  logic        emtx_wr_wait
);

  default clocking cb @(posedge txlclk_p); endclocking

  // Asynchronous reset drives outputs to idle
  assert property (@cb reset |-> (emtx_ack==1'b0 && txframe_p==8'h00 && txdata_p==64'd0));

  // All checks below disabled while reset asserted
  default disable iff (reset);

  // Frame value sanity
  assert property (@cb (txframe_p==8'h00 || txframe_p==8'h3F || txframe_p==8'hFF));

  // Ack/frame relationship
  assert property (@cb emtx_ack |-> txframe_p==8'h3F);
  assert property (@cb txframe_p==8'h3F |-> emtx_ack);

  // Ack must be caused by access (rising and level)
  assert property (@cb $rose(emtx_ack) |-> $past(emtx_access));
  assert property (@cb emtx_ack |-> $past(emtx_access));

  // Ack is a single-cycle pulse
  assert property (@cb emtx_ack |=> !emtx_ack);

  // Header emission one cycle after access when ack low
  assert property (@cb (emtx_access && !emtx_ack) |=> (emtx_ack && txframe_p==8'h3F &&
                     txdata_p == {8'h00,8'h00, ~($past(emtx_write)), 7'h00,
                                  $past(emtx_ctrlmode), $past(emtx_dstaddr[31:28]),
                                  $past(emtx_dstaddr[27:4]), $past(emtx_dstaddr[3:0]),
                                  $past(emtx_datamode), $past(emtx_write), $past(emtx_access)}));

  // Payload emission the cycle after ack was high
  assert property (@cb $past(emtx_ack) |-> (txframe_p==8'hFF &&
                                            txdata_p=={$past(emtx_data), $past(emtx_srcaddr)}));

  // Idle outputs when no access and no ack
  assert property (@cb (!emtx_access && !emtx_ack) |=> (txframe_p==8'h00 && txdata_p==64'd0));

  // Allowed frame sequencing
  assert property (@cb $past(txframe_p)==8'h3F |-> txframe_p==8'hFF);
  assert property (@cb $past(txframe_p)==8'hFF |-> (txframe_p==8'h00 || txframe_p==8'h3F));
  assert property (@cb $past(txframe_p)==8'h00 |-> (txframe_p==8'h00 || txframe_p==8'h3F));

  // If access persists through payload, next cycle must start a new header
  assert property (@cb ($past(emtx_ack) && emtx_access) |-> ##1 (emtx_ack && txframe_p==8'h3F));

  // 2-flop wait synchronizers: exactly 2-cycle delay from tx_*_wait
  assert property (@cb $past(!reset,2) |-> emtx_rd_wait == $past(tx_rd_wait,2));
  assert property (@cb $past(!reset,2) |-> emtx_wr_wait == $past(tx_wr_wait,2));

  // Coverage: header/payload/idle and transaction varieties
  cover property (@cb (emtx_access && !emtx_ack) ##1 emtx_ack ##1 !emtx_ack);                // basic transaction
  cover property (@cb (emtx_access && !emtx_ack &&  emtx_write) ##1 emtx_ack);               // write header
  cover property (@cb (emtx_access && !emtx_ack && !emtx_write) ##1 emtx_ack);               // read header
  cover property (@cb (emtx_access && !emtx_ack) ##1 emtx_ack ##1 emtx_access ##1 emtx_ack); // back-to-back
  cover property (@cb (emtx_access && !emtx_ack && (emtx_datamode==2'b00)) ##1 emtx_ack);
  cover property (@cb (emtx_access && !emtx_ack && (emtx_datamode==2'b11)) ##1 emtx_ack);
  cover property (@cb $changed(tx_rd_wait) ##2 $changed(emtx_rd_wait));
  cover property (@cb $changed(tx_wr_wait) ##2 $changed(emtx_wr_wait));

endmodule

// Bind example (instantiate once per DUT instance)
bind eproto_tx eproto_tx_sva sva_i (
  .txlclk_p     (txlclk_p),
  .reset        (reset),
  .emtx_access  (emtx_access),
  .emtx_write   (emtx_write),
  .emtx_datamode(emtx_datamode),
  .emtx_ctrlmode(emtx_ctrlmode),
  .emtx_dstaddr (emtx_dstaddr),
  .emtx_srcaddr (emtx_srcaddr),
  .emtx_data    (emtx_data),
  .tx_rd_wait   (tx_rd_wait),
  .tx_wr_wait   (tx_wr_wait),
  .emtx_ack     (emtx_ack),
  .txframe_p    (txframe_p),
  .txdata_p     (txdata_p),
  .emtx_rd_wait (emtx_rd_wait),
  .emtx_wr_wait (emtx_wr_wait)
);