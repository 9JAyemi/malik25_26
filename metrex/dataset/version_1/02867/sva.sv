// SVA for altera_up_video_scaler_shrink
bind altera_up_video_scaler_shrink scaler_shrink_sva u_sva();

module scaler_shrink_sva;
  // Bound into DUT scope; directly references DUT signals/params
  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Combinational definitions
  assert property (stream_in_ready == (stream_in_valid && (drop || !valid || transfer_data)));
  assert property (capture_inputs  == (stream_in_ready && !drop));
  assert property (transfer_data   == (!stream_out_valid && stream_in_valid && !drop));
  assert property (drop            == (drop_pixel[0] || drop_line[0]));

  // Output update protocol
  assert property (!(transfer_data || (stream_out_ready && stream_out_valid))
                   |-> $stable({stream_out_valid, stream_out_data, stream_out_startofpacket, stream_out_endofpacket}));
  assert property (transfer_data
                   |=> (stream_out_valid == $past(valid) &&
                        stream_out_data  == $past(data) &&
                        stream_out_startofpacket == $past(startofpacket) &&
                        stream_out_endofpacket   == $past(endofpacket)));
  assert property ((stream_out_ready && stream_out_valid)
                   |=> (!stream_out_valid && (stream_out_data=='0) && !stream_out_startofpacket && !stream_out_endofpacket));

  // Data-path regs
  assert property (capture_inputs
                   |=> (data          == $past(stream_in_data) &&
                        startofpacket == ($past(stream_in_startofpacket) || $past(saved_startofpacket)) &&
                        endofpacket   == $past(stream_in_endofpacket) &&
                        valid         == $past(stream_in_valid)));
  assert property ((stream_in_ready && drop)
                   |=> (endofpacket == ($past(endofpacket) || $past(stream_in_endofpacket)) &&
                        $stable({data, startofpacket, valid})));
  assert property (!stream_in_ready |-> $stable({data, startofpacket, endofpacket, valid}));

  // saved_startofpacket accumulation/clear
  assert property (capture_inputs |=> saved_startofpacket == 1'b0);
  assert property ((stream_in_ready && drop)
                   |=> saved_startofpacket == ($past(saved_startofpacket) || $past(stream_in_startofpacket)));
  assert property (!stream_in_ready |-> $stable(saved_startofpacket));

  // Width counter
  assert property (!stream_in_ready |-> $stable(width_counter));
  assert property ((stream_in_ready && (stream_in_startofpacket || (width_counter == (WIDTH_IN-1)))))
                   |=> width_counter == '0);
  assert property ((stream_in_ready && !stream_in_startofpacket && (width_counter != (WIDTH_IN-1))))
                   |=> width_counter == $past(width_counter)+1);
  assert property (width_counter < WIDTH_IN);

  // Height counter
  assert property (!stream_in_ready |-> $stable(height_counter));
  assert property ((stream_in_ready && stream_in_startofpacket) |=> height_counter == '0);
  assert property ((stream_in_ready && !stream_in_startofpacket && (width_counter == (WIDTH_IN-1))))
                   |=> height_counter == $past(height_counter)+1);
  assert property ((stream_in_ready && !stream_in_startofpacket && (width_counter != (WIDTH_IN-1))))
                   |-> $stable(height_counter));

  // Drop masks rotation
  assert property (!stream_in_ready |-> $stable(drop_pixel));
  assert property ((stream_in_ready && (stream_in_startofpacket || (width_counter == (WIDTH_IN-1)))))
                   |=> drop_pixel == WIDTH_DROP_MASK);
  assert property ((stream_in_ready && !stream_in_startofpacket && (width_counter != (WIDTH_IN-1))))
                   |=> drop_pixel == {$past(drop_pixel[2:0]), $past(drop_pixel[3])};

  assert property (!stream_in_ready |-> $stable(drop_line));
  assert property ((stream_in_ready && stream_in_startofpacket) |=> drop_line == HEIGHT_DROP_MASK);
  assert property ((stream_in_ready && !stream_in_startofpacket && (width_counter == (WIDTH_IN-1))))
                   |=> drop_line == {$past(drop_line[2:0]), $past(drop_line[3])};

  // Output flag sanity
  assert property (stream_out_startofpacket |-> stream_out_valid);
  assert property (stream_out_endofpacket   |-> stream_out_valid);

  // Coverage
  cover property (stream_in_valid && stream_in_ready && !drop);                  // captured a kept pixel
  cover property (saved_startofpacket && capture_inputs);                        // SOP saved then used
  cover property (transfer_data);                                                // transfer to output
  cover property (stream_out_valid && stream_out_ready);                         // output handshake
  cover property (stream_out_startofpacket && stream_out_valid);                 // SOP out
  cover property (stream_out_endofpacket   && stream_out_valid);                 // EOP out
  cover property (stream_in_ready && (width_counter == (WIDTH_IN-1)));           // end-of-line
  cover property (drop);                                                         // dropped pixel/line
endmodule