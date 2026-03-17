// Auto-generated bind (no bind found in SVA files)
// NOTE: Unconnected SVA ports (not in DUT): totalcnt_zero_on_reset, assert, property, rxaddr_zero_on_reset, frmcrc_zero_on_reset, eq0_high_on_reset, b1, eq0_matches_counter, disable, iff, frmcrcstateend_matches_lsb, totalcnt_reset_on_idle_no_dv, totalcnt_increments_on_mrxdv, past, totalcnt_holds_without_inc_or_rst, rxaddr_reset_on_state_reset, rxaddr_increments_on_rxvalid, rxaddr_holds_without_inc_or_rst, frmcrc_reset_on_idle, frmcrc_increments_in_crc_state, frmcrc_holds_without_inc_or_rst
bind fb_rxcounters fb_rxcounters_sva auto_sva_inst (
    .MRxClk(MRxClk),
    .Reset(Reset),
    .MRxDV(MRxDV),
    .RxValid(RxValid),
    .StateIdle(StateIdle),
    .StateFFS(StateFFS),
    .StatePreamble(StatePreamble),
    .StateData(StateData),
    .StateFrmCrc(StateFrmCrc),
    .MRxDEqDataSoC(MRxDEqDataSoC),
    .TotalRecvNibCntEq0(TotalRecvNibCntEq0),
    .TotalRecvNibCnt(TotalRecvNibCnt),
    .RxRamAddr(RxRamAddr),
    .FrmCrcNibCnt(FrmCrcNibCnt),
    .FrmCrcStateEnd(FrmCrcStateEnd),
    .posedge(posedge),
    .d0(d0),
    .d1(d1)
);
