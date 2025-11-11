// SVA for USB_JTAG + submodules
// Bind these checkers to the DUT. Focused, concise, high-signal-quality checks and coverage.

///////////////////////////////////////////////////////////////
// Top-level USB_JTAG assertions (iCLK domain)
///////////////////////////////////////////////////////////////
module USB_JTAG_SVA (
  input iCLK, iRST_n, iTxD_Start,
  input [7:0] mRxD_DATA,
  input       mRxD_Ready, mTxD_Done,
  input       Pre_RxD_Ready, Pre_TxD_Done,
  input [7:0] oRxD_DATA,
  input       oRxD_Ready, oTxD_Done
);
  default clocking cb @(posedge iCLK); endclocking
  // One-cycle pulses
  assert property (oRxD_Ready |-> ##1 !oRxD_Ready);
  assert property (oTxD_Done  |-> ##1 !oTxD_Done);

  // Reset drives outputs low in reset
  assert property (!iRST_n |-> ##0 (!oRxD_Ready && !oTxD_Done));

  // RX ready propagation and gating
  // Rising edge detect of mRxD_Ready (via Pre_RxD_Ready) when not transmitting must pulse oRxD_Ready and capture data
  assert property (( !$past(Pre_RxD_Ready) && mRxD_Ready && !iTxD_Start )
                   |-> ##0 (oRxD_Ready && (oRxD_DATA == mRxD_DATA)));
  // If TX is requested, suppress RX ready pulse
  assert property (( !$past(Pre_RxD_Ready) && mRxD_Ready &&  iTxD_Start )
                   |-> ##0 !oRxD_Ready);
  // oRxD_Ready should only assert on RX ready rising edge and when TX not starting
  assert property (oRxD_Ready |-> ( !$past(Pre_RxD_Ready) && mRxD_Ready && !iTxD_Start ));

  // TX done propagation (edge detect on mTxD_Done)
  assert property (( !$past(Pre_TxD_Done) && mTxD_Done ) |-> ##0 oTxD_Done);
  assert property (oTxD_Done |-> ( !$past(Pre_TxD_Done) && mTxD_Done ));

  // Coverage: RX edge propagates, and RX edge blocked by TX start
  cover property (( !$past(Pre_RxD_Ready) && mRxD_Ready && !iTxD_Start ) ##0 oRxD_Ready);
  cover property (( !$past(Pre_RxD_Ready) && mRxD_Ready &&  iTxD_Start ) ##0 !oRxD_Ready);
  // Coverage: TX done seen at top
  cover property (oTxD_Done);

endmodule

bind USB_JTAG USB_JTAG_SVA usb_jtag_sva_i (.*);

///////////////////////////////////////////////////////////////
// JTAG_REC assertions (TCK/TCS domain)
///////////////////////////////////////////////////////////////
module JTAG_REC_SVA (
  input TCK, TCS, TDI,
  input [7:0] oRxD_DATA,
  input       oRxD_Ready,
  input [7:0] rDATA,
  input [2:0] rCont
);
  // Async reset on TCS
  assert property (@(posedge TCS) 1 |-> ##0 (!oRxD_Ready && (rCont==3'b000)));

  // Default clock: TCK; disable in reset (TCS high)
  default clocking cb @(posedge TCK); endclocking

  // While not in reset, rCont increments modulo-8 each TCK
  assert property (disable iff (TCS) (rCont == ($past(rCont)+3'b001)));

  // oRxD_Ready relationship to rCont == 0 (use ##0 and $past to resolve NBA sampling)
  assert property (disable iff (TCS) ##0 (oRxD_Ready == ($past(rCont)==3'b000)));
  // oRxD_Ready is single-cycle
  assert property (disable iff (TCS) (oRxD_Ready |-> ##1 !oRxD_Ready));
  // Data alignment when ready pulses
  assert property (disable iff (TCS) ($past(rCont)==3'b000) |-> ##0 (oRxD_DATA == {TDI, $past(rDATA)[7:1]}));

  // No ready when in reset
  assert property (@(posedge TCK) TCS |-> ##0 !oRxD_Ready);

  // Coverage: observe periodic ready pulses
  cover property (disable iff (TCS) ($past(rCont)==3'b000) ##0 oRxD_Ready);

endmodule

bind JTAG_REC JTAG_REC_SVA jtag_rec_sva_i (.*);

///////////////////////////////////////////////////////////////
// JTAG_TRANS assertions (TCK/TCS domain)
///////////////////////////////////////////////////////////////
module JTAG_TRANS_SVA (
  input TCK, TCS, iTxD_Start,
  input [7:0] iTxD_DATA,
  input       oTxD_Done,
  input [2:0] rCont,
  input       TDO
);
  // Async reset on TCS
  assert property (@(posedge TCS) 1 |-> ##0 (!oTxD_Done && (rCont==3'b000) && (TDO==1'b0)));

  default clocking cb @(posedge TCK); endclocking

  // Counting and outputs behavior per iTxD_Start
  assert property (disable iff (TCS) ( iTxD_Start |-> ##0 (rCont == ($past(rCont)+3'b001)) ));
  assert property (disable iff (TCS) (!iTxD_Start |-> ##0 ((rCont==3'b000) && (TDO==1'b0))));

  // TDO should present bit indexed by old rCont when shifting
  assert property (disable iff (TCS) ( iTxD_Start |-> ##0 (TDO == iTxD_DATA[$past(rCont)]) ));

  // Done pulse exactly when old rCont == 7 (and single-cycle)
  assert property (disable iff (TCS) ##0 (oTxD_Done == ($past(rCont)==3'b111)));
  assert property (disable iff (TCS) (oTxD_Done |-> ##1 !oTxD_Done));

  // Coverage: 8 shifts produce done; repeated frames
  cover property (disable iff (TCS) (iTxD_Start[*8]) ##1 oTxD_Done);
  cover property (disable iff (TCS) (iTxD_Start[*16]) and (oTxD_Done [*2]));

endmodule

bind JTAG_TRANS JTAG_TRANS_SVA jtag_trans_sva_i (.*);