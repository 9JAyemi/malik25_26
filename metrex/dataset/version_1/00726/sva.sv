// SVA checker for Raster_Laser_Projector_Video_In_video_rgb_resampler_0
// Bind this file to the DUT.
// Focus: handshake correctness, stall behavior, pipeline transfer, and conversion math.

module raster_resampler_sva
  #(parameter IDW=23, ODW=7, IEW=1, OEW=0, ALPHA=10'h3FF)
  (
    input clk,
    input reset,

    input  [IDW:0] stream_in_data,
    input          stream_in_startofpacket,
    input          stream_in_endofpacket,
    input  [IEW:0] stream_in_empty,
    input          stream_in_valid,

    input          stream_out_ready,

    input          stream_in_ready,

    input  [ODW:0] stream_out_data,
    input          stream_out_startofpacket,
    input          stream_out_endofpacket,
    input  [OEW:0] stream_out_empty,
    input          stream_out_valid
  );

  // helpers
  function automatic [9:0] expand8to10(input [7:0] x);
    expand8to10 = {x, x[7:6]};
  endfunction

  function automatic [7:0] expected_gray(input [IDW:0] din);
    logic [9:0] r, g, b;
    logic [11:0] sum;
    r   = expand8to10(din[23:16]);
    g   = expand8to10(din[15: 8]);
    b   = expand8to10(din[ 7: 0]);
    sum = {2'b0, r} + {1'b0, g, 1'b0} + {2'b0, b}; // r + 2g + b
    expected_gray = sum[11:4]; // >> 4
  endfunction

  function automatic [OEW:0] trunc_empty(input [IEW:0] e);
    trunc_empty = e[OEW:0];
  endfunction

  sequence load_s;
    (stream_out_ready || !stream_out_valid);
  endsequence

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset)

  // Reset drives cleared outputs (synchronous reset block)
  assert property (@(posedge clk) disable iff (1'b0)
                   reset |-> (stream_out_data=='0 && stream_out_valid==0 &&
                              stream_out_startofpacket==0 && stream_out_endofpacket==0 &&
                              stream_out_empty=='0));

  // Ready computation is combinationally consistent with spec
  assert property (stream_in_ready == (stream_out_ready || !stream_out_valid));

  // When loading, outputs in next cycle reflect inputs from this cycle
  assert property (load_s |=> (
                    stream_out_data          == expected_gray(stream_in_data)    &&
                    stream_out_valid         == stream_in_valid                  &&
                    stream_out_startofpacket == stream_in_startofpacket          &&
                    stream_out_endofpacket   == stream_in_endofpacket            &&
                    stream_out_empty         == trunc_empty(stream_in_empty)
                  ));

  // When stalled (valid && !ready), all output signals hold their values
  assert property ((stream_out_valid && !stream_out_ready) |=> $stable({
                      stream_out_data,
                      stream_out_valid,
                      stream_out_startofpacket,
                      stream_out_endofpacket,
                      stream_out_empty
                    }));

  // During stall, upstream must see backpressure (in_ready low)
  assert property ((stream_out_valid && !stream_out_ready) |-> !stream_in_ready);

  // If output is not valid, upstream is always ready (since ~valid)
  assert property ((!stream_out_valid) |-> stream_in_ready);

  // Coverage: basic pass-through transfer
  cover property (load_s && stream_in_valid && stream_out_ready);

  // Coverage: two-cycle (or more) stall
  cover property ((stream_out_valid && !stream_out_ready)[*2]);

  // Coverage: back-to-back accepted beats (no stall)
  cover property ((load_s && stream_in_valid && stream_out_ready)
                  ##1 (load_s && stream_in_valid && stream_out_ready));

  // Coverage: SOP accepted then later EOP accepted
  sequence acc; load_s && stream_in_valid; endsequence
  cover property (acc && stream_in_startofpacket ##[1:$] acc && stream_in_endofpacket);

endmodule

bind Raster_Laser_Projector_Video_In_video_rgb_resampler_0
  raster_resampler_sva #(.IDW(IDW), .ODW(ODW), .IEW(IEW), .OEW(OEW), .ALPHA(ALPHA))
  i_raster_resampler_sva (.*);