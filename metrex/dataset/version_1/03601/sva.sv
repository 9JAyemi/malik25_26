// SVA for PCIeGen2x8If128_gtp_pipe_rate
module PCIeGen2x8If128_gtp_pipe_rate_sva #(
  parameter string PCIE_SIM_SPEEDUP = "FALSE",
  parameter int unsigned TXDATA_WAIT_MAX = 15
)(
  input  logic              RATE_CLK,
  input  logic              RATE_RST_N,

  input  logic [1:0]        RATE_RATE_IN,
  input  logic              RATE_DRP_DONE,
  input  logic              RATE_RXPMARESETDONE,
  input  logic              RATE_TXRATEDONE,
  input  logic              RATE_RXRATEDONE,
  input  logic              RATE_TXSYNC_DONE,
  input  logic              RATE_PHYSTATUS,

  input  logic              RATE_PCLK_SEL,
  input  logic              RATE_DRP_START,
  input  logic              RATE_DRP_X16,
  input  logic [2:0]        RATE_RATE_OUT,
  input  logic              RATE_TXSYNC_START,
  input  logic              RATE_DONE,
  input  logic              RATE_IDLE,
  input  logic [4:0]        RATE_FSM
);

  // Local decode of state from DUT output
  localparam int FSM_IDLE            = 0;
  localparam int FSM_TXDATA_WAIT     = 1;
  localparam int FSM_PCLK_SEL        = 2;
  localparam int FSM_DRP_X16_START   = 3;
  localparam int FSM_DRP_X16_DONE    = 4;
  localparam int FSM_RATE_SEL        = 5;
  localparam int FSM_RXPMARESETDONE  = 6;
  localparam int FSM_DRP_X20_START   = 7;
  localparam int FSM_DRP_X20_DONE    = 8;
  localparam int FSM_RATE_DONE       = 9;
  localparam int FSM_TXSYNC_START_S  = 10;
  localparam int FSM_TXSYNC_DONE     = 11;
  localparam int FSM_DONE_S          = 12;

  wire [3:0] fsm = RATE_FSM[3:0];

  // Parameter sanity
  initial assert (TXDATA_WAIT_MAX <= 15) else $error("TXDATA_WAIT_MAX exceeds counter width");

  // Basic reset values (combinationally visible at clock)
  property p_reset_defaults;
    @(posedge RATE_CLK)
    !RATE_RST_N |-> (fsm==FSM_IDLE && RATE_PCLK_SEL==1'b0 && RATE_RATE_OUT==3'd0 &&
                     RATE_IDLE && !RATE_DONE && !RATE_DRP_START && !RATE_DRP_X16 && !RATE_TXSYNC_START);
  endproperty
  assert property (p_reset_defaults);

  // No X on key outputs when out of reset
  assert property (@(posedge RATE_CLK) disable iff (!RATE_RST_N)
                   !$isunknown({fsm,RATE_PCLK_SEL,RATE_RATE_OUT,RATE_DRP_START,RATE_DRP_X16,
                                RATE_TXSYNC_START,RATE_DONE,RATE_IDLE}));

  // State field well-formed
  assert property (@(posedge RATE_CLK) RATE_FSM[4]==1'b0);
  assert property (@(posedge RATE_CLK) disable iff (!RATE_RST_N)
                   (fsm inside {[FSM_IDLE:FSM_DONE_S]}));

  // Output decode must match state
  assert property (@(posedge RATE_CLK) (RATE_IDLE  == (fsm==FSM_IDLE)));
  assert property (@(posedge RATE_CLK) (RATE_DONE  == (fsm==FSM_DONE_S)));
  assert property (@(posedge RATE_CLK) (RATE_TXSYNC_START == (fsm==FSM_TXSYNC_START_S)));
  assert property (@(posedge RATE_CLK) (RATE_DRP_START == (fsm==FSM_DRP_X16_START || fsm==FSM_DRP_X20_START)));
  assert property (@(posedge RATE_CLK) (RATE_DRP_X16   == (fsm==FSM_DRP_X16_START || fsm==FSM_DRP_X16_DONE)));

  // Legal values only for RATE_RATE_OUT (design only drives 0 or 1)
  assert property (@(posedge RATE_CLK) disable iff (!RATE_RST_N)
                   (RATE_RATE_OUT inside {3'd0,3'd1}));

  // Glitch control: pclk_sel/rate_out change only in their update states
  assert property (@(posedge RATE_CLK) disable iff (!RATE_RST_N)
                   (RATE_PCLK_SEL != $past(RATE_PCLK_SEL)) |-> ($past(fsm)==FSM_PCLK_SEL));
  assert property (@(posedge RATE_CLK) disable iff (!RATE_RST_N)
                   (RATE_RATE_OUT != $past(RATE_RATE_OUT)) |-> ($past(fsm)==FSM_RATE_SEL));

  // Hold when not in update states
  assert property (@(posedge RATE_CLK) disable iff (!RATE_RST_N)
                   (fsm!=FSM_PCLK_SEL) |-> $stable(RATE_PCLK_SEL));
  assert property (@(posedge RATE_CLK) disable iff (!RATE_RST_N)
                   (fsm!=FSM_RATE_SEL) |-> $stable(RATE_RATE_OUT));

  // Allowed next-state transitions (safety)
  assert property (@(posedge RATE_CLK) disable iff (!RATE_RST_N)
                   ($past(fsm)==FSM_IDLE) |-> (fsm==FSM_IDLE || fsm==FSM_TXDATA_WAIT));
  assert property (@(posedge RATE_CLK) disable iff (!RATE_RST_N)
                   ($past(fsm)==FSM_TXDATA_WAIT) |-> (fsm==FSM_TXDATA_WAIT || fsm==FSM_PCLK_SEL));
  // Deterministic branch from PCLK_SEL
  generate
    if (PCIE_SIM_SPEEDUP == "TRUE") begin
      assert property (@(posedge RATE_CLK) disable iff (!RATE_RST_N)
                       ($past(fsm)==FSM_PCLK_SEL) |-> (fsm==FSM_RATE_SEL));
    end else begin
      assert property (@(posedge RATE_CLK) disable iff (!RATE_RST_N)
                       ($past(fsm)==FSM_PCLK_SEL) |-> (fsm==FSM_DRP_X16_START));
    end
  endgenerate
  assert property (@(posedge RATE_CLK) disable iff (!RATE_RST_N)
                   ($past(fsm)==FSM_DRP_X16_START) |-> (fsm==FSM_DRP_X16_START || fsm==FSM_DRP_X16_DONE));
  assert property (@(posedge RATE_CLK) disable iff (!RATE_RST_N)
                   ($past(fsm)==FSM_DRP_X16_DONE) |-> (fsm==FSM_DRP_X16_DONE || fsm==FSM_RATE_SEL));
  generate
    if (PCIE_SIM_SPEEDUP == "TRUE") begin
      assert property (@(posedge RATE_CLK) disable iff (!RATE_RST_N)
                       ($past(fsm)==FSM_RATE_SEL) |-> (fsm==FSM_RATE_DONE));
    end else begin
      assert property (@(posedge RATE_CLK) disable iff (!RATE_RST_N)
                       ($past(fsm)==FSM_RATE_SEL) |-> (fsm==FSM_RXPMARESETDONE));
    end
  endgenerate
  assert property (@(posedge RATE_CLK) disable iff (!RATE_RST_N)
                   ($past(fsm)==FSM_RXPMARESETDONE) |-> (fsm==FSM_RXPMARESETDONE || fsm==FSM_DRP_X20_START));
  assert property (@(posedge RATE_CLK) disable iff (!RATE_RST_N)
                   ($past(fsm)==FSM_DRP_X20_START) |-> (fsm==FSM_DRP_X20_START || fsm==FSM_DRP_X20_DONE));
  assert property (@(posedge RATE_CLK) disable iff (!RATE_RST_N)
                   ($past(fsm)==FSM_DRP_X20_DONE) |-> (fsm==FSM_DRP_X20_DONE || fsm==FSM_RATE_DONE));
  assert property (@(posedge RATE_CLK) disable iff (!RATE_RST_N)
                   ($past(fsm)==FSM_RATE_DONE) |-> (fsm==FSM_RATE_DONE || fsm==FSM_TXSYNC_START_S));
  assert property (@(posedge RATE_CLK) disable iff (!RATE_RST_N)
                   ($past(fsm)==FSM_TXSYNC_START_S) |-> (fsm==FSM_TXSYNC_START_S || fsm==FSM_TXSYNC_DONE));
  assert property (@(posedge RATE_CLK) disable iff (!RATE_RST_N)
                   ($past(fsm)==FSM_TXSYNC_DONE) |-> (fsm==FSM_TXSYNC_DONE || fsm==FSM_DONE_S));
  assert property (@(posedge RATE_CLK) disable iff (!RATE_RST_N)
                   ($past(fsm)==FSM_DONE_S) |-> (fsm==FSM_IDLE));

  // DONE pulse semantics
  assert property (@(posedge RATE_CLK) disable iff (!RATE_RST_N)
                   RATE_DONE |-> (fsm==FSM_DONE_S && $past(fsm)==FSM_TXSYNC_DONE));
  assert property (@(posedge RATE_CLK) disable iff (!RATE_RST_N)
                   (RATE_DONE && $past(RATE_DONE)) |-> 0); // DONE must not stick

  // Coverage: visit all states
  cover property (@(posedge RATE_CLK) disable iff (!RATE_RST_N) (fsm==FSM_IDLE));
  cover property (@(posedge RATE_CLK) disable iff (!RATE_RST_N) (fsm==FSM_TXDATA_WAIT));
  cover property (@(posedge RATE_CLK) disable iff (!RATE_RST_N) (fsm==FSM_PCLK_SEL));
  cover property (@(posedge RATE_CLK) disable iff (!RATE_RST_N) (fsm==FSM_DRP_X16_START));
  cover property (@(posedge RATE_CLK) disable iff (!RATE_RST_N) (fsm==FSM_DRP_X16_DONE));
  cover property (@(posedge RATE_CLK) disable iff (!RATE_RST_N) (fsm==FSM_RATE_SEL));
  cover property (@(posedge RATE_CLK) disable iff (!RATE_RST_N) (fsm==FSM_RXPMARESETDONE));
  cover property (@(posedge RATE_CLK) disable iff (!RATE_RST_N) (fsm==FSM_DRP_X20_START));
  cover property (@(posedge RATE_CLK) disable iff (!RATE_RST_N) (fsm==FSM_DRP_X20_DONE));
  cover property (@(posedge RATE_CLK) disable iff (!RATE_RST_N) (fsm==FSM_RATE_DONE));
  cover property (@(posedge RATE_CLK) disable iff (!RATE_RST_N) (fsm==FSM_TXSYNC_START_S));
  cover property (@(posedge RATE_CLK) disable iff (!RATE_RST_N) (fsm==FSM_TXSYNC_DONE));
  cover property (@(posedge RATE_CLK) disable iff (!RATE_RST_N) (fsm==FSM_DONE_S));

  // Coverage: full flow (speedup TRUE)
  generate
    if (PCIE_SIM_SPEEDUP == "TRUE") begin
      sequence s_flow_fast;
        fsm==FSM_IDLE ##1
        fsm==FSM_TXDATA_WAIT ##1
        fsm==FSM_PCLK_SEL ##1
        fsm==FSM_RATE_SEL ##1
        fsm==FSM_RATE_DONE ##[1:$]
        fsm==FSM_TXSYNC_START_S ##1
        fsm==FSM_TXSYNC_DONE ##1
        fsm==FSM_DONE_S ##1
        fsm==FSM_IDLE;
      endsequence
      cover property (@(posedge RATE_CLK) disable iff (!RATE_RST_N) s_flow_fast);
    end else begin
      // Coverage: full flow (speedup FALSE)
      sequence s_flow_slow;
        fsm==FSM_IDLE ##1
        fsm==FSM_TXDATA_WAIT ##1
        fsm==FSM_PCLK_SEL ##1
        fsm==FSM_DRP_X16_START ##[1:$]
        fsm==FSM_DRP_X16_DONE ##[1:$]
        fsm==FSM_RATE_SEL ##1
        fsm==FSM_RXPMARESETDONE ##[1:$]
        fsm==FSM_DRP_X20_START ##[1:$]
        fsm==FSM_DRP_X20_DONE ##[1:$]
        fsm==FSM_RATE_DONE ##[1:$]
        fsm==FSM_TXSYNC_START_S ##1
        fsm==FSM_TXSYNC_DONE ##1
        fsm==FSM_DONE_S ##1
        fsm==FSM_IDLE;
      endsequence
      cover property (@(posedge RATE_CLK) disable iff (!RATE_RST_N) s_flow_slow);
    end
  endgenerate

  // Coverage: both rate settings observed and pclk_sel toggles
  cover property (@(posedge RATE_CLK) disable iff (!RATE_RST_N) (RATE_RATE_OUT==3'd0));
  cover property (@(posedge RATE_CLK) disable iff (!RATE_RST_N) (RATE_RATE_OUT==3'd1));
  cover property (@(posedge RATE_CLK) disable iff (!RATE_RST_N) (RATE_PCLK_SEL && !$past(RATE_PCLK_SEL)));
  cover property (@(posedge RATE_CLK) disable iff (!RATE_RST_N) (!RATE_PCLK_SEL && $past(RATE_PCLK_SEL)));

endmodule

// Example bind (uncomment and place in a testbench or an assertions file):
// bind PCIeGen2x8If128_gtp_pipe_rate
//   PCIeGen2x8If128_gtp_pipe_rate_sva #(
//     .PCIE_SIM_SPEEDUP(PCIE_SIM_SPEEDUP),
//     .TXDATA_WAIT_MAX(TXDATA_WAIT_MAX)
//   ) u_sva (.*);