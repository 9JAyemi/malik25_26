// SVA checker for amm_master_qsys_with_pcie_video_rgb_resampler_0
module amm_master_qsys_with_pcie_video_rgb_resampler_0_sva
  #(parameter IDW=23, ODW=29, IEW=1, OEW=1, ALPHA=10'h3FF)
  (
    input  logic                   clk,
    input  logic                   reset,

    input  logic [IDW:0]           stream_in_data,
    input  logic                   stream_in_startofpacket,
    input  logic                   stream_in_endofpacket,
    input  logic [IEW:0]           stream_in_empty,
    input  logic                   stream_in_valid,

    input  logic                   stream_out_ready,

    input  logic                   stream_in_ready,

    input  logic [ODW:0]           stream_out_data,
    input  logic                   stream_out_startofpacket,
    input  logic                   stream_out_endofpacket,
    input  logic [OEW:0]           stream_out_empty,
    input  logic                   stream_out_valid
  );

  // Parameter sanity for this checker
  initial begin
    if (IDW!=23 || ODW!=29 || IEW!=1 || OEW!=1)
      $error("SVA checker expects IDW=23, ODW=29, IEW=1, OEW=1");
  end

  default clocking cb @(posedge clk); endclocking

  // Track when $past is valid after reset
  logic past_valid;
  always_ff @(posedge clk or posedge reset) begin
    if (reset) past_valid <= 1'b0;
    else       past_valid <= 1'b1;
  end

  // Expected RGB10: {r[9:0], g[9:0], b[9:0]} from input RGB8 with MSB replication
  function automatic logic [ODW:0] conv_rgb(input logic [IDW:0] din);
    logic [9:0] r,g,b;
    begin
      r = {din[23:16], din[23:22]};
      g = {din[15: 8], din[15:14]};
      b = {din[ 7: 0], din[ 7: 6]};
      return {r,g,b};
    end
  endfunction

  // In-ready must reflect output ready/valid state
  assert property (cb disable iff (reset)
    stream_in_ready == (stream_out_ready || !stream_out_valid)
  ) else $error("stream_in_ready mismatch");

  // Reset clears outputs
  assert property (cb
    reset |-> (stream_out_data=='0 &&
               stream_out_startofpacket==1'b0 &&
               stream_out_endofpacket==1'b0 &&
               stream_out_empty=='0 &&
               stream_out_valid==1'b0)
  ) else $error("Outputs not cleared on reset");

  // Hold outputs under backpressure
  assert property (cb disable iff (reset)
    (stream_out_valid && !stream_out_ready) |=> $stable({stream_out_valid,
                                                         stream_out_startofpacket,
                                                         stream_out_endofpacket,
                                                         stream_out_empty,
                                                         stream_out_data})
  ) else $error("Outputs changed under backpressure");

  // Register update on enable (out_ready || !out_valid): flags and data propagate
  assert property (cb disable iff (reset)
    (past_valid && (stream_out_ready || !stream_out_valid)) |=> (
        stream_out_valid          == $past(stream_in_valid)          &&
        stream_out_startofpacket  == $past(stream_in_startofpacket)  &&
        stream_out_endofpacket    == $past(stream_in_endofpacket)    &&
        stream_out_empty          == $past(stream_in_empty)          &&
        stream_out_data           == conv_rgb($past(stream_in_data))
    )
  ) else $error("Register/update mapping incorrect");

  // If input transfer occurs, out_valid must assert next cycle
  assert property (cb disable iff (reset)
    (past_valid && stream_in_valid && stream_in_ready) |=> stream_out_valid
  ) else $error("out_valid did not assert after accepted input");

  // When stalled, stream_in_ready must be low (implied by ready eq, but explicit)
  assert property (cb disable iff (reset)
    (stream_out_valid && !stream_out_ready) |-> !stream_in_ready
  ) else $error("stream_in_ready high during backpressure");

  // No X on outputs when valid
  assert property (cb disable iff (reset)
    stream_out_valid |-> !$isunknown({stream_out_data,
                                      stream_out_startofpacket,
                                      stream_out_endofpacket,
                                      stream_out_empty})
  ) else $error("X/Z on outputs while valid");

  // Coverage: at least one input transfer
  cover property (cb disable iff (reset)
    stream_in_valid && stream_in_ready
  );

  // Coverage: backpressure then release
  cover property (cb disable iff (reset)
    (stream_out_valid && !stream_out_ready)
    ##1 (stream_out_valid && !stream_out_ready)[*1:$]
    ##1 (stream_out_valid &&  stream_out_ready)
  );

  // Coverage: SOP to EOP on output with actual transfers
  cover property (cb disable iff (reset)
    (stream_out_valid && stream_out_ready && stream_out_startofpacket)
    ##[1:$] (stream_out_valid && stream_out_ready && stream_out_endofpacket)
  );

  // Coverage: update when out_valid=0 even if out_ready=0 (bubble fill)
  cover property (cb disable iff (reset)
    (!stream_out_valid && !stream_out_ready)
    ##1 stream_out_valid
  );

endmodule

// Bind into the DUT
bind amm_master_qsys_with_pcie_video_rgb_resampler_0
  amm_master_qsys_with_pcie_video_rgb_resampler_0_sva #(.IDW(IDW), .ODW(ODW), .IEW(IEW), .OEW(OEW), .ALPHA(ALPHA))
  amm_master_qsys_with_pcie_video_rgb_resampler_0_sva_i
  (.*);