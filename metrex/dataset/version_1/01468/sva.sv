// SVA for pcie_core_gtp_pipe_rate
// Bind this module to your DUT instance.
// Example:
// bind pcie_core_gtp_pipe_rate pcie_core_gtp_pipe_rate_sva #(.PCIE_SIM_SPEEDUP(PCIE_SIM_SPEEDUP), .TXDATA_WAIT_MAX(TXDATA_WAIT_MAX)) u_sva (.*);

module pcie_core_gtp_pipe_rate_sva #(
  parameter string PCIE_SIM_SPEEDUP = "FALSE",
  parameter int unsigned TXDATA_WAIT_MAX = 15
)(
  input               RATE_CLK,
  input               RATE_RST_N,
  input       [ 1:0]  RATE_RATE_IN,
  input               RATE_DRP_DONE,
  input               RATE_RXPMARESETDONE,
  input               RATE_TXRATEDONE,
  input               RATE_RXRATEDONE,
  input               RATE_TXSYNC_DONE,
  input               RATE_PHYSTATUS,

  input               RATE_PCLK_SEL,
  input               RATE_DRP_START,
  input               RATE_DRP_X16,
  input       [ 2:0]  RATE_RATE_OUT,
  input               RATE_TXSYNC_START,
  input               RATE_DONE,
  input               RATE_IDLE,
  input       [ 4:0]  RATE_FSM
);

  localparam bit SIM = (PCIE_SIM_SPEEDUP == "TRUE");

  // State encoding (low 4 bits of RATE_FSM)
  localparam int S_IDLE            = 0;
  localparam int S_TXDATA_WAIT     = 1;
  localparam int S_PCLK_SEL        = 2;
  localparam int S_DRP_X16_START   = 3;
  localparam int S_DRP_X16_DONE    = 4;
  localparam int S_RATE_SEL        = 5;
  localparam int S_RXPMARESETDONE  = 6;
  localparam int S_DRP_X20_START   = 7;
  localparam int S_DRP_X20_DONE    = 8;
  localparam int S_RATE_DONE       = 9;
  localparam int S_TXSYNC_START    = 10;
  localparam int S_TXSYNC_DONE     = 11;
  localparam int S_DONE            = 12;

  function automatic bit in_state (int s);
    return RATE_FSM[3:0] == s[3:0];
  endfunction

  // Default clocking and reset
  default clocking cb @(posedge RATE_CLK); endclocking
  default disable iff (!RATE_RST_N);

  // Reset values
  assert property ( !RATE_RST_N |-> (in_state(S_IDLE) && RATE_IDLE && !RATE_DONE &&
                                     (RATE_FSM[4] == 1'b0) && (RATE_PCLK_SEL == 1'b0) &&
                                     (RATE_RATE_OUT == 3'd0) && !RATE_DRP_START && !RATE_DRP_X16 && !RATE_TXSYNC_START) );

  // RATE_FSM MSB must be 0
  assert property ( RATE_FSM[4] == 1'b0 );

  // Output decode correctness
  assert property ( RATE_DRP_START == (in_state(S_DRP_X16_START) || in_state(S_DRP_X20_START)) );
  assert property ( RATE_DRP_X16   == (in_state(S_DRP_X16_START) || in_state(S_DRP_X16_DONE)) );
  assert property ( RATE_TXSYNC_START == in_state(S_TXSYNC_START) );
  assert property ( RATE_DONE == in_state(S_DONE) );
  assert property ( RATE_IDLE == in_state(S_IDLE) );

  // PCLK_SEL only changes in PCLK_SEL state and equals 2-cycle-delayed RATE_RATE_IN==1 there
  assert property ( $changed(RATE_PCLK_SEL) |-> in_state(S_PCLK_SEL) );
  assert property ( in_state(S_PCLK_SEL) |-> (RATE_PCLK_SEL == ($past(RATE_RATE_IN,2) == 2'd1)) );

  // RATE_OUT constraints
  assert property ( RATE_RATE_OUT <= 3'd1 ); // Only 0 or 1 allowed
  assert property ( $changed(RATE_RATE_OUT) |-> in_state(S_RATE_SEL) );
  assert property ( in_state(S_RATE_SEL) |-> (RATE_RATE_OUT == (($past(RATE_RATE_IN,2) == 2'd1) ? 3'd1 : 3'd0)) );

  // IDLE transition driven by 2-stage sampled RATE_RATE_IN mismatch
  assert property ( in_state(S_IDLE) && ($past(RATE_RATE_IN,2) != $past(RATE_RATE_IN,1)) |=> in_state(S_TXDATA_WAIT) );
  assert property ( in_state(S_IDLE) && ($past(RATE_RATE_IN,2) == $past(RATE_RATE_IN,1)) |=> in_state(S_IDLE) );

  // TXDATA_WAIT stays exactly TXDATA_WAIT_MAX+1 cycles, then PCLK_SEL
  assert property (
    $rose(in_state(S_TXDATA_WAIT)) |->
      in_state(S_TXDATA_WAIT)[* (TXDATA_WAIT_MAX+1)] ##1 in_state(S_PCLK_SEL)
  );

  // PCLK_SEL next state depends on SIM
  generate
    if (SIM) begin
      assert property ( in_state(S_PCLK_SEL) |=> in_state(S_RATE_SEL) );
    end else begin
      assert property ( in_state(S_PCLK_SEL) |=> in_state(S_DRP_X16_START) );
    end
  endgenerate

  // DRP_X16 handshake (using 2-cycle sampled RATE_DRP_DONE)
  assert property (
    in_state(S_DRP_X16_START) |=> (
      (in_state(S_DRP_X16_DONE)  && ($past(RATE_DRP_DONE,2) == 1'b0)) ||
      (in_state(S_DRP_X16_START) && ($past(RATE_DRP_DONE,2) == 1'b1))
    )
  );
  assert property (
    in_state(S_DRP_X16_DONE) |=> (
      (in_state(S_RATE_SEL)      && ($past(RATE_DRP_DONE,2) == 1'b1)) ||
      (in_state(S_DRP_X16_DONE)  && ($past(RATE_DRP_DONE,2) == 1'b0))
    )
  );

  // RATE_SEL next state depends on SIM
  generate
    if (SIM) begin
      assert property ( in_state(S_RATE_SEL) |=> in_state(S_RATE_DONE) );
    end else begin
      assert property ( in_state(S_RATE_SEL) |=> in_state(S_RXPMARESETDONE) );
    end
  endgenerate

  // RXPMARESETDONE deassert-wait gating to DRP_X20_START (2-cycle sampled)
  assert property (
    in_state(S_RXPMARESETDONE) |=> (
      (in_state(S_DRP_X20_START)    && ($past(RATE_RXPMARESETDONE,2) == 1'b0)) ||
      (in_state(S_RXPMARESETDONE)   && ($past(RATE_RXPMARESETDONE,2) == 1'b1))
    )
  );

  // DRP_X20 handshake (using 2-cycle sampled RATE_DRP_DONE)
  assert property (
    in_state(S_DRP_X20_START) |=> (
      (in_state(S_DRP_X20_DONE)  && ($past(RATE_DRP_DONE,2) == 1'b0)) ||
      (in_state(S_DRP_X20_START) && ($past(RATE_DRP_DONE,2) == 1'b1))
    )
  );
  assert property (
    in_state(S_DRP_X20_DONE) |=> (
      (in_state(S_RATE_DONE)      && ($past(RATE_DRP_DONE,2) == 1'b1)) ||
      (in_state(S_DRP_X20_DONE)   && ($past(RATE_DRP_DONE,2) == 1'b0))
    )
  );

  // TXSYNC handshake (using 2-cycle sampled RATE_TXSYNC_DONE)
  assert property (
    in_state(S_TXSYNC_START) |=> (
      (in_state(S_TXSYNC_DONE)    && ($past(RATE_TXSYNC_DONE,2) == 1'b0)) ||
      (in_state(S_TXSYNC_START)   && ($past(RATE_TXSYNC_DONE,2) == 1'b1))
    )
  );
  assert property (
    in_state(S_TXSYNC_DONE) |=> (
      (in_state(S_DONE)           && ($past(RATE_TXSYNC_DONE,2) == 1'b1)) ||
      (in_state(S_TXSYNC_DONE)    && ($past(RATE_TXSYNC_DONE,2) == 1'b0))
    )
  );

  // DONE -> IDLE unconditionally
  assert property ( in_state(S_DONE) |=> in_state(S_IDLE) );

  // Coverage: full successful flow (conditional on SIM)
  generate
    if (!SIM) begin : COV_SLOW
      cover property (
        in_state(S_IDLE)
        ##1 in_state(S_TXDATA_WAIT)[* (TXDATA_WAIT_MAX+1)]
        ##1 in_state(S_PCLK_SEL)
        ##1 in_state(S_DRP_X16_START)
        ##1 in_state(S_DRP_X16_DONE)
        ##1 in_state(S_RATE_SEL)
        ##1 in_state(S_RXPMARESETDONE)
        ##1 in_state(S_DRP_X20_START)
        ##1 in_state(S_DRP_X20_DONE)
        ##1 in_state(S_RATE_DONE)
        ##[1:$] in_state(S_TXSYNC_START)
        ##1 in_state(S_TXSYNC_DONE)
        ##1 in_state(S_DONE)
        ##1 in_state(S_IDLE)
      );
    end else begin : COV_FAST
      cover property (
        in_state(S_IDLE)
        ##1 in_state(S_TXDATA_WAIT)[* (TXDATA_WAIT_MAX+1)]
        ##1 in_state(S_PCLK_SEL)
        ##1 in_state(S_RATE_SEL)
        ##1 in_state(S_RATE_DONE)
        ##[1:$] in_state(S_TXSYNC_START)
        ##1 in_state(S_TXSYNC_DONE)
        ##1 in_state(S_DONE)
        ##1 in_state(S_IDLE)
      );
    end
  endgenerate

  // Coverage: rate change 0->1 drives PCLK_SEL=1 in PCLK_SEL
  cover property (
    in_state(S_IDLE) && ($past(RATE_RATE_IN,2) != $past(RATE_RATE_IN,1)) && ($past(RATE_RATE_IN,2) == 2'd1)
    ##[1:$] in_state(S_PCLK_SEL) && (RATE_PCLK_SEL == 1'b1)
  );

  // Coverage: rate change 1->0 drives PCLK_SEL=0 in PCLK_SEL
  cover property (
    in_state(S_IDLE) && ($past(RATE_RATE_IN,2) != $past(RATE_RATE_IN,1)) && ($past(RATE_RATE_IN,2) != 2'd1)
    ##[1:$] in_state(S_PCLK_SEL) && (RATE_PCLK_SEL == 1'b0)
  );

  // Coverage: RATE_RATE_OUT updates in RATE_SEL to match 2-cycle-delayed RATE_RATE_IN
  cover property (
    in_state(S_RATE_SEL) && (RATE_RATE_OUT == (($past(RATE_RATE_IN,2) == 2'd1) ? 3'd1 : 3'd0))
  );

endmodule