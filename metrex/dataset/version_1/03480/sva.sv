// SVA for NPM_Toggle_PHY_B_Reset
// Bind into the DUT; checks FSM, outputs, timer, and handshakes concisely.

module NPM_Toggle_PHY_B_Reset_sva;

  default clocking cb @(posedge iSystemClock); endclocking
  default disable iff (iReset);

  // Basic sanity
  assert property ($onehot(rPBR_cur_state));
  assert property ($onehot(rPBR_nxt_state));

  // Cur state must follow nxt state
  assert property (rPBR_cur_state == $past(rPBR_nxt_state));

  // Next-state decoding correctness
  assert property ((rPBR_cur_state==PBR_RESET) |-> (rPBR_nxt_state==PBR_READY));
  assert property ((rPBR_cur_state==PBR_READY) |-> (rPBR_nxt_state==(iStart ? PBR_RFRST : PBR_READY)));
  assert property ((rPBR_cur_state==PBR_RFRST) |-> (rPBR_nxt_state==PBR_RLOOP));
  assert property ((rPBR_cur_state==PBR_RLOOP && !wJOBDone) |-> (rPBR_nxt_state==PBR_RLOOP));
  assert property ((rPBR_cur_state==PBR_RLOOP &&  wJOBDone) |-> (rPBR_nxt_state==(iStart ? PBR_RFRST : PBR_READY)));

  // wJOBDone definition
  assert property (wJOBDone == (rTimer[3:0]==4'hA));

  // Timer behavior
  assert property ((rPBR_nxt_state==PBR_RLOOP) |-> rTimer == $past(rTimer)+1);
  assert property ((rPBR_nxt_state inside {PBR_RESET,PBR_READY,PBR_RFRST}) |-> rTimer==4'h0);

  // Output register values vs nxt-state encoding
  assert property ((rPBR_nxt_state==PBR_RESET) |->
                   (!rReady && rTimer==0 && !rPI_BUFF_Reset && !rPI_BUFF_RE && !rPI_BUFF_WE && rPO_DQStrobe==8'h00 && !rDQSOutEnable));
  assert property ((rPBR_nxt_state==PBR_READY) |->
                   ( rReady && rTimer==0 && !rPI_BUFF_Reset && !rPI_BUFF_RE && !rPI_BUFF_WE && rPO_DQStrobe==8'h00 && !rDQSOutEnable));
  assert property ((rPBR_nxt_state==PBR_RFRST) |->
                   (!rReady && rTimer==0 &&  rPI_BUFF_Reset && !rPI_BUFF_RE && !rPI_BUFF_WE && rPO_DQStrobe==8'h55 &&  rDQSOutEnable));
  assert property ((rPBR_nxt_state==PBR_RLOOP) |->
                   (!rReady             &&  rPI_BUFF_Reset && !rPI_BUFF_RE && !rPI_BUFF_WE && rPO_DQStrobe==8'h55 &&  rDQSOutEnable));

  // rReady/ready/laststep logic
  assert property (rReady == (rPBR_nxt_state==PBR_READY));
  assert property (oReady == (rReady | wJOBDone));
  assert property (oLastStep == wJOBDone);

  // Output mirrors
  assert property (oPI_BUFF_Reset == rPI_BUFF_Reset);
  assert property (oPI_BUFF_RE    == rPI_BUFF_RE);
  assert property (oPI_BUFF_WE    == rPI_BUFF_WE);
  assert property (oPO_DQStrobe   == rPO_DQStrobe);
  assert property (oDQSOutEnable  == rDQSOutEnable);

  // No X after reset released
  assert property (!$isunknown({rPBR_cur_state,rPBR_nxt_state,rTimer,rReady,
                                rPI_BUFF_Reset,rPI_BUFF_RE,rPI_BUFF_WE,rPO_DQStrobe,rDQSOutEnable,
                                oReady,oLastStep,oPI_BUFF_Reset,oPI_BUFF_RE,oPI_BUFF_WE,oPO_DQStrobe,oDQSOutEnable,wJOBDone})));

  // Async reset effects (immediate)
  always @(posedge iReset) begin
    assert (rPBR_cur_state==PBR_RESET);
    assert (!rReady && rTimer==0 && !rPI_BUFF_Reset && !rPI_BUFF_RE && !rPI_BUFF_WE && rPO_DQStrobe==8'h00 && !rDQSOutEnable);
  end

  // Functional coverage
  cover property (rPBR_cur_state==PBR_RESET ##1 rPBR_cur_state==PBR_READY);
  cover property ((rPBR_cur_state==PBR_READY && iStart) ##1 (rPBR_cur_state==PBR_RFRST) ##1 (rPBR_cur_state==PBR_RLOOP));
  cover property ((rPBR_cur_state==PBR_RLOOP, rTimer==4'hA, !iStart) ##1 (rPBR_cur_state==PBR_READY));
  cover property ((rPBR_cur_state==PBR_RLOOP, rTimer==4'hA,  iStart) ##1 (rPBR_cur_state==PBR_RFRST));

endmodule

bind NPM_Toggle_PHY_B_Reset NPM_Toggle_PHY_B_Reset_sva sva_inst();