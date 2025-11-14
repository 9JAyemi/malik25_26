// SVA for video_sys_Video_RGB_Resampler
// Bind this to the DUT; concise, high-quality checks and useful coverage.

bind video_sys_Video_RGB_Resampler video_sys_Video_RGB_Resampler_sva
  #(.IDW(IDW), .ODW(ODW), .IEW(IEW), .OEW(OEW), .ALPHA(ALPHA)) sva_i (.*);

module video_sys_Video_RGB_Resampler_sva
  #(parameter IDW=23, ODW=15, IEW=1, OEW=0, parameter ALPHA=10'h3FF)
  (
    input clk, reset,

    input [IDW:0] stream_in_data,
    input         stream_in_startofpacket,
    input         stream_in_endofpacket,
    input [IEW:0] stream_in_empty,
    input         stream_in_valid,

    input         stream_out_ready,
    input         stream_in_ready,

    input [ODW:0] stream_out_data,
    input         stream_out_startofpacket,
    input         stream_out_endofpacket,
    input [OEW:0] stream_out_empty,
    input         stream_out_valid,

    // internal DUT nets (visible for bind (.*))
    input [9:0]   r,g,b,a,
    input [ODW:0] converted_data
  );

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Basic structural/comb checks
  assert property (stream_in_ready == (stream_out_ready || !stream_out_valid));
  assert property (!$isunknown({stream_out_valid,stream_out_data,stream_out_startofpacket,
                                stream_out_endofpacket,stream_out_empty,stream_in_ready}));

  // Reset behavior (one-cycle after reset asserted)
  assert property (reset |=> (!stream_out_valid &&
                              !stream_out_startofpacket && !stream_out_endofpacket &&
                              stream_out_data=='0 && stream_out_empty=='0));

  // Conversion wiring sanity
  assert property (a == ALPHA);
  assert property (r == {stream_in_data[23:16], stream_in_data[23:22]});
  assert property (g == {stream_in_data[15: 8], stream_in_data[15:14]});
  assert property (b == {stream_in_data[ 7: 0], stream_in_data[ 7: 6]});
  assert property (converted_data[15:11]==r[9:5] &&
                   converted_data[10: 5]==g[9:4] &&
                   converted_data[ 4: 0]==b[9:5]);

  // Register update when allowed (copies all fields)
  property p_update;
    (stream_out_ready || !stream_out_valid) |=> (
      stream_out_valid            == $past(stream_in_valid) &&
      stream_out_startofpacket    == $past(stream_in_startofpacket) &&
      stream_out_endofpacket      == $past(stream_in_endofpacket) &&
      stream_out_empty            == $past(stream_in_empty[OEW:0]) &&
      // Data mapping (RGB888 -> RGB565)
      stream_out_data[15:11]      == $past(stream_in_data[23:19]) &&
      stream_out_data[10: 5]      == $past(stream_in_data[15:10]) &&
      stream_out_data[ 4: 0]      == $past(stream_in_data[ 7: 3]) &&
      // Matches DUT internal converted_data
      stream_out_data             == $past(converted_data)
    );
  endproperty
  assert property (p_update);

  // Stall behavior: hold outputs, backpressure asserted
  assert property ((stream_out_valid && !stream_out_ready) |-> !stream_in_ready);
  assert property ((stream_out_valid && !stream_out_ready)
                   |=> $stable({stream_out_valid,stream_out_data,
                                stream_out_startofpacket,stream_out_endofpacket,stream_out_empty}));

  // If input empty is wider than output, upper bits must be zero when updating (no silent truncation)
  generate if (IEW > OEW) begin
    assert property ((stream_out_ready || !stream_out_valid)
                     |-> (stream_in_empty[IEW:OEW+1] == '0));
  end endgenerate

  // Useful coverage
  cover property (stream_in_valid && stream_in_ready);                                   // any transfer
  cover property (stream_in_valid && stream_in_ready && stream_in_startofpacket);        // SOP transfer
  cover property (stream_in_valid && stream_in_ready && stream_in_endofpacket);          // EOP transfer
  cover property (stream_out_valid && !stream_out_ready ##1
                  stream_out_valid && !stream_out_ready ##1
                  stream_out_ready && stream_in_valid);                                  // multi-cycle stall then xfer
  cover property (!stream_out_valid ##1 (stream_out_ready || !stream_out_valid)
                  ##1 stream_out_valid);                                                 // update from idle
  cover property (stream_out_valid && stream_out_ready && stream_in_valid);              // update while valid due to ready

endmodule