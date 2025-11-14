// SVA for altera_avalon_st_packets_to_bytes
// Bind into the DUT; references internal signals directly

module altera_avalon_st_packets_to_bytes_sva #(
  parameter int CHANNEL_WIDTH = 8,
  parameter int ENCODING      = 0
) ();

  // Convenience
  function automatic bit is_rsvd8 (logic [7:0] b);
    return (b==8'h7a || b==8'h7b || b==8'h7c || b==8'h7d);
  endfunction

  // Handshake "fires" when DUT will emit a byte
  wire fire = (out_ready || !out_valid) && in_valid;

  default clocking cb @(posedge clk); endclocking
  default disable iff (!reset_n);

  // Basic reset/sanity
  assert property (!reset_n |-> !out_valid && out_data==8'h00);
  assert property (in_ready |-> in_valid);
  assert property (fire |-> out_valid);

  // Priority of emitted control symbols (CHANNEL first, then SOP, EOP, ESC, else data)
  if (CHANNEL_WIDTH > 0) begin
    // Channel header first
    assert property (fire && need_channel && !sent_channel && !sent_channel_char |-> out_data==8'h7c);

    // SOP/EOP/ESC ordering when no channel pending
    assert property (fire && !(need_channel && !sent_channel) && need_sop && !sent_sop |-> out_data==8'h7a);
    assert property (fire && !(need_channel && !sent_channel) && !(need_sop && !sent_sop) && need_eop && !sent_eop |-> out_data==8'h7b);
    assert property (fire && !(need_channel && !sent_channel) && !(need_sop && !sent_sop) && !(need_eop && !sent_eop) && need_esc && !sent_esc |-> out_data==8'h7d);

    // Payload value when no headers pending (escaped iff previous cycle emitted data ESC)
    assert property (fire &&
                     !(need_channel && !sent_channel) && !(need_sop && !sent_sop) &&
                     !(need_eop && !sent_eop) && !(need_esc && !sent_esc)
                     |-> out_data == ($past(sent_esc) ? (in_data ^ 8'h20) : in_data));

    // Data escape semantics: after emitting ESC for data, next payload is XOR 0x20 of that in_data
    assert property (fire && !(need_channel && !sent_channel) &&
                           !(need_sop && !sent_sop) && !(need_eop && !sent_eop) &&
                           need_esc && !sent_esc ##1
                     fire && !(need_channel && !sent_channel) &&
                           !(need_sop && !sent_sop) && !(need_eop && !sent_eop)
                     |-> out_data == ($past(in_data) ^ 8'h20));

    // Channel bookkeeping: when channel is marked sent, latch stored_channel
    assert property (sent_channel |=> stored_channel == $past(in_channel));

    // Channel content checks per ENCODING
    if (ENCODING == 0) begin
      // After 0x7c: if channel byte is reserved -> ESC then escaped byte; else raw byte
      assert property (fire && need_channel && !sent_channel && !sent_channel_char ##1
                       fire |-> (is_rsvd8($past(in_channel)) ? (out_data==8'h7d) : (out_data==$past(in_channel))));
      assert property (fire && need_channel && !sent_channel && !sent_channel_char && is_rsvd8(in_channel) ##1
                       fire ##1 fire |-> out_data == ($past(in_channel,2) ^ 8'h20));
    end else begin
      // ENCODING==1: channel bytes have MSB=1 until last chunk, then MSB=0
      assert property (fire && need_channel && !sent_channel && sent_channel_char && (channel_count>0) |-> out_data[7]==1'b1);
      assert property (fire && need_channel && !sent_channel && sent_channel_char && (channel_count==0) |-> out_data[7]==1'b0);
      // If channel ESC is emitted, it must be the escape symbol
      assert property (fire && need_channel && !sent_channel && channel_needs_esc && !channel_escaped |-> out_data==8'h7d);
    end
  end else begin
    // CHANNEL_WIDTH==0 path
    assert property (fire && need_channel && !sent_channel && !sent_channel_char |-> out_data==8'h7c);
    assert property (fire && need_channel && !sent_channel && sent_channel_char |-> out_data==8'h00);

    assert property (fire && !(need_channel && !sent_channel) && need_sop && !sent_sop |-> out_data==8'h7a);
    assert property (fire && !(need_channel && !sent_channel) && !(need_sop && !sent_sop) && need_eop && !sent_eop |-> out_data==8'h7b);
    assert property (fire && !(need_channel && !sent_channel) && !(need_sop && !sent_sop) && !(need_eop && !sent_eop) && need_esc && !sent_esc |-> out_data==8'h7d);

    assert property (fire &&
                     !(need_channel && !sent_channel) && !(need_sop && !sent_sop) &&
                     !(need_eop && !sent_eop) && !(need_esc && !sent_esc)
                     |-> out_data == ($past(sent_esc) ? (in_data ^ 8'h20) : in_data));
  end

  // If SOP and EOP are requested together (no channel), SOP must precede EOP
  assert property (fire && !(need_channel && !sent_channel) && need_sop && !sent_sop && need_eop && !sent_eop |-> out_data==8'h7a);
  assert property (fire && !(need_channel && !sent_channel) && need_sop && !sent_sop && need_eop && !sent_eop ##1
                   fire |-> out_data==8'h7b);

  // Coverage: see each control symbol, a data escape, and channel paths
  cover property (reset_n && fire && out_data==8'h7a);
  cover property (reset_n && fire && out_data==8'h7b);
  cover property (reset_n && fire && out_data==8'h7c);
  cover property (reset_n && fire && out_data==8'h7d);
  cover property (reset_n && fire &&
                  !(need_channel && !sent_channel) && !(need_sop && !sent_sop) &&
                  !(need_eop && !sent_eop) && $past(need_esc && !sent_esc) &&
                  out_data == ($past(in_data) ^ 8'h20));
  if (CHANNEL_WIDTH > 0) begin
    cover property (reset_n && fire && need_channel && !sent_channel && !sent_channel_char ##1 fire && !is_rsvd8($past(in_channel)));
    if (ENCODING==0)
      cover property (reset_n && fire && need_channel && !sent_channel && !sent_channel_char && is_rsvd8(in_channel) ##1 fire ##1 fire);
  end

endmodule

bind altera_avalon_st_packets_to_bytes
  altera_avalon_st_packets_to_bytes_sva #(.CHANNEL_WIDTH(CHANNEL_WIDTH), .ENCODING(ENCODING)) i_altera_avalon_st_packets_to_bytes_sva();