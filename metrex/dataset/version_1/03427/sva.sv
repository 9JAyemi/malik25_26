// SVA for joy_control
// Bind into the DUT so we can see internals
bind joy_control joy_control_sva jc_sva();

module joy_control_sva;

  default clocking cb @(negedge CLK); endclocking
  default disable iff ($initstate)

  // Legal state range
  assert property (pState <= 4);

  // Output decode by state
  assert property (SS == !(pState inside {1,2,3}));
  assert property (getByte == (pState == 1));

  // State 0: idle/clear
  assert property (pState == 0 |-> SS && !getByte && tmpSR==40'd0 && byteCnt==3'd0);
  assert property (pState == 0 && !sndRec |=> pState == 0);
  assert property (pState == 0 &&  sndRec |=> pState == 1);

  // State 1: request byte, count handshakes
  assert property (pState == 1 &&  BUSY |=> pState == 2 && byteCnt == $past(byteCnt)+1);
  assert property (pState == 1 && !BUSY |=> pState == 1 && byteCnt == $past(byteCnt));

  // State 2: wait while BUSY
  assert property (pState == 2 &&  BUSY |=> pState == 2);
  assert property (pState == 2 && !BUSY |=> pState == 3);

  // State 3: capture/shift, branch by byteCnt
  assert property (pState == 3 |=> tmpSR == {$past(tmpSR)[31:0], $past(RxData)});
  assert property (pState == 3 && byteCnt == 5 |=> pState == 4);
  assert property (pState == 3 && byteCnt != 5 |=> pState == 1);

  // State 4: done/hold until sndRec deasserts, update DOUT
  assert property (pState == 4 |-> SS && !getByte);
  assert property (pState == 4 |=> DOUT == $past(tmpSR));
  assert property (pState == 4 &&  sndRec |=> pState == 4);
  assert property (pState == 4 && !sndRec |=> pState == 0);

  // Byte counter bounds
  assert property (byteCnt <= 5);

  // Change-only-where-expected
  assert property ($changed(tmpSR)  |-> $past(pState) inside {0,3});
  assert property ($changed(DOUT)   |-> $past(pState) == 4);
  assert property ($changed(byteCnt)|-> ($past(pState)==0) || ($past(pState)==1 && $past(BUSY)));

  // Stability constraints
  assert property ((pState inside {1,2,3}) |=> SS==1'b0);
  assert property ((pState inside {0,4})   |=> SS==1'b1);
  assert property ((pState != 4) |=> DOUT == $past(DOUT));

  // Coverage: complete 5-byte transaction 0 -> (1,2,3)x5 -> 4 -> 0
  sequence one_byte;
    (pState==1) ##1 (pState==2)[*1:$] ##1 (pState==3);
  endsequence
  cover property (pState==0 ##1 sndRec ##1 one_byte[*5] ##1 (pState==4) ##1 (pState==0));

  // Coverage: hold in state 4 while sndRec stays high
  cover property (pState==4 && sndRec ##1 (pState==4 && sndRec)[*3]);

endmodule