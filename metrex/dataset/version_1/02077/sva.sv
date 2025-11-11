// SVA for image_processor_dbg
// Bind this checker to the DUT to verify key behaviors concisely.

module image_processor_dbg_sva (
  input  logic         iClk,
  input  logic         iLineValid,
  input  logic         iFrameValid,
  input  logic         iSW,
  input  logic [23:0]  oDebug,

  // internal DUT signals (connect via bind)
  input  logic [23:0]  rDebugFPS,
  input  logic [23:0]  rDebugRes,
  input  logic [23:0]  rFPS,
  input  logic [32:0]  rTime,
  input  logic [23:0]  rWidth,
  input  logic [23:0]  rHeight,
  input  logic         rLineValidL,
  input  logic         rFrameValidL
);

  localparam logic [32:0] TIME_WRAP = 33'd25_000_000;

  bit past_valid;
  always_ff @(posedge iClk) past_valid <= 1'b1;

  default clocking cb @(posedge iClk); endclocking
  default disable iff (!past_valid);

  // Muxed debug output selection
  assert property (iSW ? (oDebug == rDebugFPS) : (oDebug == rDebugRes));

  // 1-cycle delayed strobes
  assert property (rLineValidL  == $past(iLineValid));
  assert property (rFrameValidL == $past(iFrameValid));

  // rTime free-runs and wraps at TIME_WRAP
  assert property ( ($past(rTime) == TIME_WRAP) |-> (rTime == 33'd0) );
  assert property ( ($past(rTime) != TIME_WRAP) |-> (rTime == $past(rTime) + 1) );

  // FPS counter and snapshot on wrap
  assert property ( ($past(rTime) == TIME_WRAP) |-> (rDebugFPS == $past(rFPS)) );
  assert property ( ($past(rTime) == TIME_WRAP) |-> (rFPS == 24'd0) );
  assert property ( ($past(rTime) != TIME_WRAP && $fell(iFrameValid)) |-> (rFPS == $past(rFPS) + 1) );
  assert property ( ($past(rTime) != TIME_WRAP && !$fell(iFrameValid)) |-> (rFPS == $past(rFPS)) );

  // Width measurement across a line
  assert property ( $rose(iLineValid) |-> (rWidth == 24'd0) );
  assert property ( ( iLineValid &&  $past(iLineValid)) |-> (rWidth == $past(rWidth) + 1) );
  assert property ( (!iLineValid && !$past(iLineValid)) |-> (rWidth == 24'd0) );
  assert property ( $fell(iLineValid) |-> (rWidth == $past(rWidth)) );
  // Latch width into upper half of rDebugRes on line fall; otherwise stable
  assert property ( $fell(iLineValid) |-> (rDebugRes[23:12] == $past(rWidth[11:0])) );
  assert property ( !$fell(iLineValid) |-> (rDebugRes[23:12] == $past(rDebugRes[23:12])) );

  // Height measurement across a frame (increment on each line fall while frame valid)
  assert property ( $rose(iFrameValid) |-> (rHeight == 24'd0) );
  assert property ( (!iFrameValid && !$past(iFrameValid)) |-> (rHeight == 24'd0) );
  assert property ( ( iFrameValid &&  $past(iFrameValid) && $fell(iLineValid)) |-> (rHeight == $past(rHeight) + 1) );
  assert property ( ( iFrameValid &&  $past(iFrameValid) && !$fell(iLineValid)) |-> (rHeight == $past(rHeight)) );
  assert property ( $fell(iFrameValid) |-> (rHeight == $past(rHeight)) );
  // Latch height into lower half of rDebugRes on frame fall; otherwise stable
  assert property ( $fell(iFrameValid) |-> (rDebugRes[11:0] == $past(rHeight[11:0])) );
  assert property ( !$fell(iFrameValid) |-> (rDebugRes[11:0] == $past(rDebugRes[11:0])) );

  // Coverage: line/width measured and latched
  cover property ( $rose(iLineValid) ##1 (iLineValid && $past(iLineValid)) [*2] ##1 $fell(iLineValid) );
  // Coverage: frame/height measured and latched
  cover property ( $rose(iFrameValid) ##[1:$] $fell(iLineValid) ##[1:$] $fell(iLineValid) ##1 $fell(iFrameValid) );
  // Coverage: FPS counted and time window wrap/transfer
  cover property ( ($past(rTime) == TIME_WRAP) ##1 (rTime == 0 && rDebugFPS == $past(rFPS)) );
  // Coverage: switch toggles output source
  cover property ( iSW == 0 ##1 iSW == 1 ##1 iSW == 0 );

endmodule

// Bind to DUT (connects internal signals by name)
bind image_processor_dbg image_processor_dbg_sva sva_ipdbg (
  .iClk       (iClk),
  .iLineValid (iLineValid),
  .iFrameValid(iFrameValid),
  .iSW        (iSW),
  .oDebug     (oDebug),

  .rDebugFPS  (rDebugFPS),
  .rDebugRes  (rDebugRes),
  .rFPS       (rFPS),
  .rTime      (rTime),
  .rWidth     (rWidth),
  .rHeight    (rHeight),
  .rLineValidL(rLineValidL),
  .rFrameValidL(rFrameValidL)
);