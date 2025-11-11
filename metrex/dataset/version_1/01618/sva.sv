// SVA for eth_rxcounters
// Bind this checker to the DUT:
// bind eth_rxcounters eth_rxcounters_sva sva_inst();

module eth_rxcounters_sva;

  // Default clock/reset
  default clocking cb @(posedge MRxClk); endclocking
  default disable iff (Reset);

  // -----------------------------
  // Basic reset checks (async reset observed on clock edge)
  // -----------------------------
  assert property (@(posedge MRxClk) Reset |-> (ByteCnt==16'h0 && IFGCounter==5'h0 && DlyCrcCnt==4'h0));

  // -----------------------------
  // ByteCnt semantics
  // -----------------------------
  // Next-state behavior
  assert property (ResetByteCounter |=> (ByteCnt==16'h0));
  assert property (IncrementByteCounter |=> (ByteCnt==$past(ByteCnt)+16'h1));
  assert property (!(ResetByteCounter || IncrementByteCounter) |=> (ByteCnt==$past(ByteCnt)));

  // Output mapping (combinational)
  assert property (DlyCrcEn |-> (ByteCntOut == (ByteCnt + 16'd4)));
  assert property (!DlyCrcEn |-> (ByteCntOut == ByteCnt));

  // Flag correctness
  assert property (ByteCntEq0 == (ByteCnt==16'h0));
  assert property (ByteCntEq1 == (ByteCnt==16'h1));
  assert property (ByteCntEq2 == (ByteCnt==16'h2));
  assert property (ByteCntEq3 == (ByteCnt==16'h3));
  assert property (ByteCntEq4 == (ByteCnt==16'h4));
  assert property (ByteCntEq5 == (ByteCnt==16'h5));
  assert property (ByteCntEq6 == (ByteCnt==16'h6));
  assert property (ByteCntEq7 == (ByteCnt==16'h7));
  assert property (ByteCntGreat2 == (ByteCnt>16'h2));
  assert property (ByteCntSmall7 == (ByteCnt<16'h7));
  assert property (ByteCntMax == (ByteCnt==16'hffff));
  assert property (ByteCntMaxFrame == ((ByteCnt==MaxFL[15:0]) && !HugEn));

  // -----------------------------
  // IFGCounter semantics
  // -----------------------------
  assert property (ResetIFGCounter |=> (IFGCounter==5'h0));
  assert property (IncrementIFGCounter |=> (IFGCounter==$past(IFGCounter)+5'h1));
  assert property (!(ResetIFGCounter || IncrementIFGCounter) |=> (IFGCounter==$past(IFGCounter)));
  assert property (IFGCounterEq24 == ((IFGCounter==5'h18) || r_IFG));
  assert property (IFGCounterEq24 |-> !IncrementIFGCounter);

  // -----------------------------
  // DlyCrcCnt semantics
  // -----------------------------
  // Range
  assert property (DlyCrcCnt <= 4'h9);

  // Priority order and transitions
  assert property ((DlyCrcCnt==4'h9) |=> (DlyCrcCnt==4'h0));
  assert property ((DlyCrcCnt!=4'h9) && (DlyCrcEn && StateSFD) |=> (DlyCrcCnt==4'h1));
  assert property ((DlyCrcCnt!=4'h9) && (DlyCrcEn && !StateSFD) && (DlyCrcCnt!=4'h0) |=> (DlyCrcCnt==$past(DlyCrcCnt)+4'h1));
  assert property (!((DlyCrcCnt==4'h9) || (DlyCrcEn && StateSFD) || (DlyCrcEn && (DlyCrcCnt!=4'h0))) |=> (DlyCrcCnt==$past(DlyCrcCnt)));

  // -----------------------------
  // Transmitting combinational definition
  // -----------------------------
  assert property (Transmitting == ((StateData[0] && ByteCntGreat2) || (StateData[1] && ByteCntSmall7)));

  // -----------------------------
  // Functional coverages
  // -----------------------------
  // ByteCnt reaches MaxFL and triggers frame max reset path
  cover property (MRxDV && StateData[0] && !HugEn && (ByteCnt==MaxFL) ##1 ResetByteCounter);

  // IFGCounter naturally counts to 24 without r_IFG
  cover property (!r_IFG throughout (!IFGCounterEq24) [*] ##1 (IFGCounter==5'h18) && IFGCounterEq24);

  // IFGCounterEq24 forced by r_IFG
  cover property ($rose(r_IFG) && IFGCounter!=5'h18 && IFGCounterEq24);

  // DlyCrcCnt start, increment, wrap
  cover property ((DlyCrcEn && StateSFD) ##1 (DlyCrcCnt==4'h1)
                  ##[1:9] (DlyCrcCnt==4'h9) ##1 (DlyCrcCnt==4'h0));

  // ByteCntOut mode switch coverage
  cover property ($rose(DlyCrcEn) and (ByteCntOut == (ByteCnt + 16'd4)));
  cover property ($fell(DlyCrcEn) and (ByteCntOut == ByteCnt));

  // Transmitting set via both branches
  cover property (StateData[0] && (ByteCnt>16'd2) && Transmitting);
  cover property (StateData[1] && (ByteCnt<16'd7) && Transmitting);

  // Early byte flags coverage
  cover property (ByteCntEq0 && ByteCntEq1 ##1 ByteCntEq2 ##1 ByteCntEq3 ##1 ByteCntEq4 ##1 ByteCntEq5 ##1 ByteCntEq6 ##1 ByteCntEq7);

endmodule