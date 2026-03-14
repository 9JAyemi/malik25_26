module fb_rxcounters_sva (
   input logic MRxClk,
   input logic Reset,
   input logic MRxDV,
   input logic RxValid,
   input logic StateIdle,
   input logic StateFFS,
   input logic StatePreamble,
   input logic [1:0] StateData,
   input logic StateFrmCrc,
   input logic MRxDEqDataSoC,
   input logic TotalRecvNibCntEq0,
   input logic [15:0] TotalRecvNibCnt,
   input logic [7:0] RxRamAddr,
   input logic [3:0] FrmCrcNibCnt,
   input logic FrmCrcStateEnd
);
   ///// Global reset effects (active-high, async) /////
   // On Reset, TotalRecvNibCnt must be 0.
   totalcnt_zero_on_reset: assert property (
      @(posedge MRxClk) Reset |-> (TotalRecvNibCnt == 16'd0)
   );
   // On Reset, RxRamAddr must be 0.
   rxaddr_zero_on_reset: assert property (
      @(posedge MRxClk) Reset |-> (RxRamAddr == 8'd0)
   );
   // On Reset, FrmCrcNibCnt must be 0.
   frmcrc_zero_on_reset: assert property (
      @(posedge MRxClk) Reset |-> (FrmCrcNibCnt == 4'd0)
   );
   // On Reset, TotalRecvNibCntEq0 must be 1.
   eq0_high_on_reset: assert property (
      @(posedge MRxClk) Reset |-> (TotalRecvNibCntEq0 == 1'b1)
   );

   ///// Combinational outputs reflect registered values /////
   // TotalRecvNibCntEq0 equals (TotalRecvNibCnt == 0).
   eq0_matches_counter: assert property (
      @(posedge MRxClk) disable iff (Reset) (TotalRecvNibCntEq0 == (TotalRecvNibCnt == 16'd0))
   );
   // FrmCrcStateEnd equals LSB of FrmCrcNibCnt.
   frmcrcstateend_matches_lsb: assert property (
      @(posedge MRxClk) disable iff (Reset) (FrmCrcStateEnd == FrmCrcNibCnt[0])
   );

   ///// TotalRecvNibCnt behavior /////
   // When StateIdle && !MRxDV, counter resets to 0 on next cycle.
   totalcnt_reset_on_idle_no_dv: assert property (
      @(posedge MRxClk) disable iff (Reset) (StateIdle && !MRxDV) |-> ##1 (TotalRecvNibCnt == 16'd0)
   );
   // When MRxDV, counter increments by 1 on next cycle.
   totalcnt_increments_on_mrxdv: assert property (
      @(posedge MRxClk) disable iff (Reset) MRxDV |-> ##1 (TotalRecvNibCnt == $past(TotalRecvNibCnt) + 16'd1)
   );
   // When !MRxDV and not idle, counter holds its value.
   totalcnt_holds_without_inc_or_rst: assert property (
      @(posedge MRxClk) disable iff (Reset) (!MRxDV && !StateIdle) |-> ##1 (TotalRecvNibCnt == $past(TotalRecvNibCnt))
   );

   ///// RxRamAddr behavior /////
   // When StateIdle/StateFFS/StatePreamble, address resets to 0 on next cycle.
   rxaddr_reset_on_state_reset: assert property (
      @(posedge MRxClk) disable iff (Reset) (StateIdle || StateFFS || StatePreamble) |-> ##1 (RxRamAddr == 8'd0)
   );
   // When RxValid and not in reset states, address increments by 1 on next cycle.
   rxaddr_increments_on_rxvalid: assert property (
      @(posedge MRxClk) disable iff (Reset) (RxValid && !(StateIdle || StateFFS || StatePreamble)) |-> ##1 (RxRamAddr == $past(RxRamAddr) + 8'd1)
   );
   // When not incrementing and not resetting, address holds its value.
   rxaddr_holds_without_inc_or_rst: assert property (
      @(posedge MRxClk) disable iff (Reset) (!RxValid && !(StateIdle || StateFFS || StatePreamble)) |-> ##1 (RxRamAddr == $past(RxRamAddr))
   );

   ///// FrmCrcNibCnt behavior /////
   // When StateIdle, CRC nibble counter resets to 0 on next cycle.
   frmcrc_reset_on_idle: assert property (
      @(posedge MRxClk) disable iff (Reset) StateIdle |-> ##1 (FrmCrcNibCnt == 4'd0)
   );
   // When StateFrmCrc and not idle, CRC nibble counter increments by 1 on next cycle.
   frmcrc_increments_in_crc_state: assert property (
      @(posedge MRxClk) disable iff (Reset) (StateFrmCrc && !StateIdle) |-> ##1 (FrmCrcNibCnt == $past(FrmCrcNibCnt) + 4'd1)
   );
   // When not in CRC state and not idle, CRC nibble counter holds its value.
   frmcrc_holds_without_inc_or_rst: assert property (
      @(posedge MRxClk) disable iff (Reset) (!StateFrmCrc && !StateIdle) |-> ##1 (FrmCrcNibCnt == $past(FrmCrcNibCnt))
   );
endmodule