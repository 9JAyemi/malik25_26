// SVA for ethtx_realign
// Bind this into the DUT: bind ethtx_realign ethtx_realign_sva sva();

module ethtx_realign_sva;
  // We are bound inside ethtx_realign and can see its signals
  localparam RE_IDLE = 0;
  localparam RE_HELD = 1;
  localparam RE_DONE = 2;

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset || clear)

  // Sanity/encoding
  assert property (@cb) state inside {RE_IDLE, RE_HELD, RE_DONE};

  // Reset effects (check even when reset is asserted)
  assert property (@(posedge clk) disable iff (1'b0)
                   (reset || clear) |=> (state==RE_IDLE && held==0 && held_occ==0 && held_sof==0));

  // Register capture/hold
  assert property (@cb) (!xfer_in) |=> $stable(held) && $stable(held_occ) && $stable(held_sof));
  assert property (@cb) xfer_in |=> (held==$past(datain[15:0]) &&
                                     held_occ==$past(datain[35:34]) &&
                                     held_sof==$past(datain[32]));

  // State transitions
  // IDLE
  assert property (@cb) (state==RE_IDLE && xfer_in && eof_in) |=> state==RE_DONE);
  assert property (@cb) (state==RE_IDLE && xfer_in && !eof_in && sof_in) |=> state==RE_HELD);
  assert property (@cb) (state==RE_IDLE && !xfer_in) |=> state==RE_IDLE);
  assert property (@cb) (state==RE_IDLE && xfer_in && !eof_in && !sof_in) |=> state==RE_IDLE);
  // HELD
  assert property (@cb) (state==RE_HELD && xfer_in && xfer_out && eof_in &&
                         (occ_in[1]^occ_in[0])) |=> state==RE_IDLE);
  assert property (@cb) (state==RE_HELD && xfer_in && xfer_out && eof_in &&
                        !(occ_in[1]^occ_in[0])) |=> state==RE_DONE);
  assert property (@cb) (state==RE_HELD && !(xfer_in && xfer_out && eof_in)) |=> state==RE_HELD);
  // DONE
  assert property (@cb) (state==RE_DONE && xfer_out) |=> state==RE_IDLE);
  assert property (@cb) (state==RE_DONE && !xfer_out) |=> state==RE_DONE);

  // Output gating vs state
  assert property (@cb) (state==RE_IDLE) |-> (dst_rdy_o && !src_rdy_o));
  assert property (@cb) (state==RE_DONE) |-> (src_rdy_o && !dst_rdy_o));
  assert property (@cb) (state==RE_HELD) |-> (dst_rdy_o==dst_rdy_i && src_rdy_o==src_rdy_i));

  // Data path composition
  assert property (@cb) dataout[31:16] == datain[31:16]);
  assert property (@cb) dataout[15:0]  == held);
  assert property (@cb) dataout[32]    == held_sof);

  // eof_out semantics encoded in dataout[33]
  assert property (@cb) (state==RE_HELD) |-> (dataout[33] == (eof_in & (occ_in[1]^occ_in[0]))));
  assert property (@cb) (state==RE_DONE) |-> (dataout[33] == 1'b1));
  assert property (@cb) (state==RE_IDLE) |-> (dataout[33] == 1'b0));

  // occ_out semantics encoded in dataout[35:34]
  assert property (@cb) (state==RE_DONE)  |-> (dataout[35:34] == (held_occ ^ 2'b10)));
  assert property (@cb) (state!=RE_DONE)  |-> (dataout[35:34] == (datain[35:34] ^ 2'b10)));

  // Handshake correctness and stability
  assert property (@cb) (xfer_in  == (src_rdy_i & dst_rdy_o));
  assert property (@cb) (xfer_out == (src_rdy_o & dst_rdy_i));
  // Upstream must hold when we deassert ready (environmental assumption)
  assume property (@cb) (!dst_rdy_o) |-> ($stable(datain) && $stable(src_rdy_i)));
  // When we offer data but sink stalls, our output stays stable
  assert property (@cb) (src_rdy_o && !dst_rdy_i) |=> $stable(dataout));

  // No X on outputs when advertising valid
  assert property (@cb) src_rdy_o |-> !$isunknown(dataout));
  assert property (@cb) !$isunknown({src_rdy_o,dst_rdy_o}));

  // Coverage
  // SOF path, occ_low=1, completes back to IDLE directly
  cover property (@cb)
    (state==RE_IDLE) ##1 (xfer_in && sof_in) ##1 (state==RE_HELD)
    ##[1:5] (xfer_in && xfer_out && eof_in && (occ_in[1]^occ_in[0]))
    ##1 (state==RE_IDLE));

  // SOF path, occ_low=0, goes to DONE then drains
  cover property (@cb)
    (state==RE_IDLE) ##1 (xfer_in && sof_in) ##1 (state==RE_HELD)
    ##[1:5] (xfer_in && xfer_out && eof_in && !(occ_in[1]^occ_in[0]))
    ##1 (state==RE_DONE) ##[1:5] xfer_out ##1 (state==RE_IDLE));

  // Direct EOF in IDLE path
  cover property (@cb)
    (state==RE_IDLE) ##1 (xfer_in && eof_in) ##1 (state==RE_DONE)
    ##[1:5] xfer_out ##1 (state==RE_IDLE));

  // DONE backpressure then accept
  cover property (@cb)
    (state==RE_DONE && !dst_rdy_i)[*3] ##1 (dst_rdy_i) ##1 (xfer_out) ##1 (state==RE_IDLE));
endmodule

bind ethtx_realign ethtx_realign_sva sva();