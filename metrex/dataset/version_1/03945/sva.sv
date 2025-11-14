// SVA for pcie_7x_v1_8_gtp_pipe_reset
// Drop inside the module or bind to it; uses internal regs and params.

`ifndef SYNTHESIS
`ifdef SVA

// convenient constants
localparam [PCIE_LANE-1:0] ALL1 = {PCIE_LANE{1'b1}};
localparam [PCIE_LANE-1:0] ALL0 = {PCIE_LANE{1'b0}};

// Default clock
default clocking cb @(posedge RST_CLK); endclocking

// ------------- Basic sanity / knownness -------------
assert property (cb RST_RST_N |-> !$isunknown({fsm,RST_CPLLRESET,RST_CPLLPD,RST_GTRESET,RST_USERRDY,RST_TXSYNC_START,RST_IDLE,RST_FSM,cfg_wait_cnt}));
// FSM one-hot (9 LSBs) and upper bits zero
assert property (cb disable iff (!RST_RST_N) $onehot(fsm[8:0]) && (fsm[10:9]==2'b00));
// Output mirrors internal FSM
assert property (cb disable iff (!RST_RST_N) RST_FSM == fsm);

// ------------- Reset behavior -------------
assert property (cb !RST_RST_N |=> (fsm==FSM_CFG_WAIT) && (cfg_wait_cnt==6'd0) &&
                               (pllreset==1'b0) && (pllpd==1'b0) && (gtreset==1'b0) && (userrdy==1'b0));
assert property (cb !RST_RST_N |=> {plllock_reg1,plllock_reg2,mmcm_lock_reg1,mmcm_lock_reg2} == 4'b0000);
assert property (cb !RST_RST_N |=> {rate_idle_reg1,rate_idle_reg2,rxcdrlock_reg1,rxcdrlock_reg2,resetdone_reg1,resetdone_reg2,phystatus_reg1,phystatus_reg2,txsync_done_reg1,txsync_done_reg2} ==
                                   {ALL0,ALL0,ALL0,ALL0,ALL0,ALL0,ALL0,ALL0,ALL0,ALL0});

// ------------- Two-flop CDC sampling on RST_CLK -------------
assert property (cb disable iff (!RST_RST_N) $past(RST_RST_N) |-> plllock_reg1==$past(RST_PLLLOCK)        && plllock_reg2==$past(plllock_reg1));
assert property (cb disable iff (!RST_RST_N) $past(RST_RST_N) |-> rate_idle_reg1==$past(RST_RATE_IDLE)    && rate_idle_reg2==$past(rate_idle_reg1));
assert property (cb disable iff (!RST_RST_N) $past(RST_RST_N) |-> rxcdrlock_reg1==$past(RST_RXCDRLOCK)    && rxcdrlock_reg2==$past(rxcdrlock_reg1));
assert property (cb disable iff (!RST_RST_N) $past(RST_RST_N) |-> mmcm_lock_reg1==$past(RST_MMCM_LOCK)    && mmcm_lock_reg2==$past(mmcm_lock_reg1));
assert property (cb disable iff (!RST_RST_N) $past(RST_RST_N) |-> resetdone_reg1==$past(RST_RESETDONE)    && resetdone_reg2==$past(resetdone_reg1));
assert property (cb disable iff (!RST_RST_N) $past(RST_RST_N) |-> phystatus_reg1==$past(RST_PHYSTATUS)    && phystatus_reg2==$past(phystatus_reg1));
assert property (cb disable iff (!RST_RST_N) $past(RST_RST_N) |-> txsync_done_reg1==$past(RST_TXSYNC_DONE)&& txsync_done_reg2==$past(txsync_done_reg1));

// ------------- CFG_WAIT counter behavior -------------
assert property (cb disable iff (!RST_RST_N)
  (fsm==FSM_CFG_WAIT && cfg_wait_cnt<CFG_WAIT_MAX) |=> (cfg_wait_cnt==$past(cfg_wait_cnt)+6'd1 && fsm==FSM_CFG_WAIT));
assert property (cb disable iff (!RST_RST_N)
  (fsm==FSM_CFG_WAIT && cfg_wait_cnt==CFG_WAIT_MAX) |=> (cfg_wait_cnt==CFG_WAIT_MAX && fsm==FSM_PLLRESET));
assert property (cb disable iff (!RST_RST_N)
  (fsm!=FSM_CFG_WAIT) |=> (cfg_wait_cnt==6'd0));

// ------------- State outputs/invariants -------------
assert property (cb disable iff (!RST_RST_N) (fsm==FSM_PLLRESET) |-> (RST_CPLLRESET && RST_GTRESET));
assert property (cb disable iff (!RST_RST_N) (fsm==FSM_PLLLOCK)  |-> (!RST_CPLLRESET));
assert property (cb disable iff (!RST_RST_N) (fsm==FSM_GTRESET)  |-> (!RST_GTRESET));
assert property (cb disable iff (!RST_RST_N) (fsm==FSM_MMCM_LOCK) |-> (RST_USERRDY == (mmcm_lock_reg2 && (BYPASS_RXCDRLOCK || &rxcdrlock_reg2))));
assert property (cb disable iff (!RST_RST_N) RST_TXSYNC_START == (fsm==FSM_TXSYNC_START));
assert property (cb disable iff (!RST_RST_N) RST_IDLE == (fsm==FSM_IDLE));
// CPLL powerdown is never asserted by this RTL
assert property (cb RST_CPLLPD==1'b0);

// USERRDY monotonic once asserted (until reset)
assert property (cb disable iff (!RST_RST_N) RST_USERRDY |=> RST_USERRDY);

// ------------- Legal next-state transitions -------------
// CFG_WAIT
assert property (cb disable iff (!RST_RST_N)
  (fsm==FSM_CFG_WAIT && cfg_wait_cnt<CFG_WAIT_MAX) |=> fsm==FSM_CFG_WAIT);
assert property (cb disable iff (!RST_RST_N)
  (fsm==FSM_CFG_WAIT && cfg_wait_cnt==CFG_WAIT_MAX) |=> fsm==FSM_PLLRESET);

// PLLRESET
assert property (cb disable iff (!RST_RST_N)
  (fsm==FSM_PLLRESET && (~plllock_reg2) && (&(~resetdone_reg2))) |=> fsm==FSM_PLLLOCK);
// stay allowed otherwise
assert property (cb disable iff (!RST_RST_N)
  (fsm==FSM_PLLRESET && !(~plllock_reg2 && (&(~resetdone_reg2)))) |=> fsm==FSM_PLLRESET);

// PLLLOCK
assert property (cb disable iff (!RST_RST_N)
  (fsm==FSM_PLLLOCK && plllock_reg2) |=> fsm==FSM_GTRESET);
assert property (cb disable iff (!RST_RST_N)
  (fsm==FSM_PLLLOCK && !plllock_reg2) |=> fsm==FSM_PLLLOCK);

// GTRESET
assert property (cb disable iff (!RST_RST_N) (fsm==FSM_GTRESET) |=> fsm==FSM_MMCM_LOCK);

// MMCM_LOCK
assert property (cb disable iff (!RST_RST_N)
  (fsm==FSM_MMCM_LOCK && mmcm_lock_reg2 && (BYPASS_RXCDRLOCK || &rxcdrlock_reg2)) |=> fsm==FSM_RESETDONE);
assert property (cb disable iff (!RST_RST_N)
  (fsm==FSM_MMCM_LOCK && !(mmcm_lock_reg2 && (BYPASS_RXCDRLOCK || &rxcdrlock_reg2))) |=> fsm==FSM_MMCM_LOCK);

// RESETDONE
assert property (cb disable iff (!RST_RST_N)
  (fsm==FSM_RESETDONE && (&resetdone_reg2) && (&(~phystatus_reg2))) |=> fsm==FSM_TXSYNC_START);
assert property (cb disable iff (!RST_RST_N)
  (fsm==FSM_RESETDONE && !((&resetdone_reg2) && (&(~phystatus_reg2)))) |=> fsm==FSM_RESETDONE);

// TXSYNC_START
assert property (cb disable iff (!RST_RST_N)
  (fsm==FSM_TXSYNC_START && (&(~txsync_done_reg2))) |=> fsm==FSM_TXSYNC_DONE);
assert property (cb disable iff (!RST_RST_N)
  (fsm==FSM_TXSYNC_START && !( &(~txsync_done_reg2))) |=> fsm==FSM_TXSYNC_START);

// TXSYNC_DONE
assert property (cb disable iff (!RST_RST_N)
  (fsm==FSM_TXSYNC_DONE && (&txsync_done_reg2)) |=> fsm==FSM_IDLE);
assert property (cb disable iff (!RST_RST_N)
  (fsm==FSM_TXSYNC_DONE && !(&txsync_done_reg2)) |=> fsm==FSM_TXSYNC_DONE);

// IDLE holds unless reset
assert property (cb disable iff (!RST_RST_N)
  (fsm==FSM_IDLE) |=> fsm==FSM_IDLE);

// Output-to-state consistency
assert property (cb disable iff (!RST_RST_N) RST_CPLLRESET |-> fsm==FSM_PLLRESET);
assert property (cb disable iff (!RST_RST_N) RST_GTRESET   |-> (fsm==FSM_PLLRESET || fsm==FSM_PLLLOCK));

// ------------- Cross-clock reset propagation -------------
clocking cb_rx @(posedge RST_RXUSRCLK); endclocking
clocking cb_d  @(posedge RST_DCLK);     endclocking

// When pllreset sampled high, the domain resets assert immediately
assert property (cb_rx pllreset |-> RST_RXUSRCLK_RESET);
assert property (cb_d  pllreset |-> RST_DCLK_RESET);

// On pllreset fall (as seen in that domain), reset deasserts one cycle later
assert property (cb_rx $fell(pllreset) |-> RST_RXUSRCLK_RESET ##1 !RST_RXUSRCLK_RESET);
assert property (cb_d  $fell(pllreset) |-> RST_DCLK_RESET     ##1 !RST_DCLK_RESET);

// ------------- Coverage -------------
// Golden path to IDLE (non-bypass)
cover property (cb disable iff (!RST_RST_N)
  (fsm==FSM_CFG_WAIT) ##[1:$] (cfg_wait_cnt==CFG_WAIT_MAX) ##1
  (fsm==FSM_PLLRESET) ##1 (~plllock_reg2 && (&(~resetdone_reg2))) ##1
  (fsm==FSM_PLLLOCK)  ##[1:$] (plllock_reg2) ##1
  (fsm==FSM_GTRESET)  ##1 (fsm==FSM_MMCM_LOCK) ##1
  (mmcm_lock_reg2 && (&rxcdrlock_reg2)) ##1
  (fsm==FSM_RESETDONE) ##1 ((&resetdone_reg2) && (&(~phystatus_reg2))) ##1
  (fsm==FSM_TXSYNC_START) ##1 (&(~txsync_done_reg2)) ##1
  (fsm==FSM_TXSYNC_DONE) ##1 (&txsync_done_reg2) ##1
  (fsm==FSM_IDLE)
);

// Bypass path (only meaningful if BYPASS_RXCDRLOCK==1)
cover property (cb disable iff (!RST_RST_N)
  (BYPASS_RXCDRLOCK==1) and (fsm==FSM_MMCM_LOCK) ##1
  (mmcm_lock_reg2 && !(&rxcdrlock_reg2)) ##1 (fsm==FSM_RESETDONE)
);

// Observe GTRESET pulse and release
cover property (cb disable iff (!RST_RST_N) (fsm==FSM_PLLRESET && RST_GTRESET) ##[1:$] (fsm==FSM_GTRESET && !RST_GTRESET));

// Observe RXUSRCLK_RESET deassertion latency after pllreset fall
cover property (cb_rx $fell(pllreset) ##1 !RST_RXUSRCLK_RESET);

`endif
`endif