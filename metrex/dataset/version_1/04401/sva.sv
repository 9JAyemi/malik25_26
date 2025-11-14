// SVA for packet_resizer_variable
// Bind this checker to the DUT instance: bind packet_resizer_variable packet_resizer_variable_sva sva();

module packet_resizer_variable_sva;

  // Use DUT scope signals via bind
  // clock/reset come from DUT
  default clocking cb @(posedge clk); endclocking

  // In-reset register values
  assert property (@(posedge clk) reset |-> (count==16'd1 && first_packet_in_burst==1'b1));

  // Disable the rest during reset
  default disable iff (reset);

  // Simple pass-through/mirroring
  assert property (o_tvalid == i_tvalid);
  assert property (i_tready == o_tready);
  assert property (o_tdata  == i_tdata);

  // tuser field mapping
  assert property (o_tuser[127:126] == i_tuser[127:126]);                        // TYPE
  assert property (o_tuser[125]     == (i_tuser[125] & first_packet_in_burst));  // TSI gated
  assert property (o_tuser[124]     == (i_tuser[124] & i_tlast));                // EOB gated by i_tlast
  assert property (o_tuser[123:112] == i_tuser[123:112]);                        // SEQ
  assert property (o_tuser[111:96]  == i_tuser[111:96]);                         // LEN
  assert property (o_tuser[95:80]   == i_tuser[79:64]);                          // SRC <- DST_in
  assert property (o_tuser[79:64]   == next_dst_sid);                            // DST <- next_dst_sid
  assert property (o_tuser[63:0]    == i_tuser[63:0]);                           // TIME
  assert property (o_tuser[125] |-> first_packet_in_burst);                      // TSI_out only on first

  // o_tlast equation and implications
  assert property (o_tlast == ((count==pkt_size) || (i_tuser[124] & i_tlast)));
  assert property ((o_tlast && !(i_tuser[124] & i_tlast)) |-> (count==pkt_size));
  assert property (o_tuser[124] |-> i_tlast); // EOB_out implies i_tlast

  // Count behavior
  assert property ((o_tvalid && o_tready && !o_tlast) |=> (count == $past(count)+16'd1));
  assert property ((o_tvalid && o_tready &&  o_tlast) |=> (count == 16'd1));
  assert property (!(o_tvalid && o_tready)            |=> (count == $past(count)));
  assert property (count >= 16'd1);

  // first_packet_in_burst behavior
  assert property ((o_tvalid && o_tready && o_tlast) |=> (first_packet_in_burst == (i_tuser[124] & i_tlast)));
  assert property (!(o_tvalid && o_tready && o_tlast) |=> (first_packet_in_burst == $past(first_packet_in_burst)));

  // Output stability under backpressure
  assert property ((o_tvalid && !o_tready) |=> $stable({o_tdata,o_tuser,o_tlast,o_tvalid}));

  // Coverage
  cover property (o_tvalid && o_tready);                                    // any transfer
  cover property (o_tvalid && o_tready && !o_tlast);                        // mid-burst transfer
  cover property (o_tvalid && o_tready && o_tlast && !(i_tuser[124]&i_tlast)); // size-based end
  cover property (o_tvalid && o_tready && (i_tuser[124]&i_tlast));          // EOB-based end
  cover property (o_tvalid && o_tready && first_packet_in_burst &&
                  i_tuser[125] && o_tuser[125]);                             // TSI on first pkt
  cover property (o_tvalid && o_tready &&
                  (o_tuser[95:80]==i_tuser[79:64]) && (o_tuser[79:64]==next_dst_sid)); // SRC/DST swap

endmodule