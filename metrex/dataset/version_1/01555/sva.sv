// SVA for Gateway
// Bind this to the DUT: bind Gateway Gateway_SVA SVA_GATEWAY();

module Gateway_SVA;

  default clocking cb @(posedge Clock); endclocking
  default disable iff (Reset);

  // Address/decode sanity
  assert property (!(pollingControlIn && pollingControlOut));
  assert property (!(readingData && writingData));

  // Simple combinational mirrors
  assert property (DataInReady == ~controlInReady);
  assert property (DataOut     ==  dataOutReg);
  assert property (DataOutValid==  dataOutValid);

  // Reset values
  assert property (Reset |-> (!controlInReady && !dataOutValid));

  // dataInReg captures only on uartDataInTransfer
  assert property (uartDataInTransfer |=> dataInReg == $past(DataIn));
  assert property ($changed(dataInReg) |-> $past(uartDataInTransfer));

  // dataOutReg captures only on CPU write
  assert property (writingData |=> dataOutReg == $past(ProcessorDataIn[7:0]));
  assert property ($changed(dataOutReg) |-> $past(writingData));

  // dataOutValid behavior (priority: read holds, write asserts, idle deasserts)
  assert property (readingData |=> $stable(dataOutValid));
  assert property ((!readingData &&  writingData) |=>  dataOutValid);
  assert property ((!readingData && !writingData) |=> !dataOutValid);

  // ProcessorDataOut priority/values
  // - Poll OUT wins and returns dataOutReg
  assert property (pollingControlOut |=> ProcessorDataOut == {24'h0, $past(dataOutReg)});
  // - No polls: return controlInReady
  assert property (!pollingControlOut && !pollingControlIn
                   |=> ProcessorDataOut == {24'h0, $past(controlInReady)});
  // - Poll IN: if simultaneous read, return dataInReg; otherwise hold value
  assert property (pollingControlIn &&  readingData
                   |=> ProcessorDataOut == {24'h0, $past(dataInReg)});
  assert property (pollingControlIn && !readingData
                   |=> $stable(ProcessorDataOut));

  // controlInReady can only rise due to poll-in (and only clears by Reset)
  assert property ($rose(controlInReady) |-> $past(pollingControlIn));

  // Handshake sanity
  assert property (uartDataInTransfer |-> (DataInValid && DataInReady));

  // Coverage
  cover property (uartDataInTransfer);
  cover property (writingData);
  cover property (pollingControlOut);
  cover property (pollingControlIn);
  cover property (readingData && pollingControlIn);
  cover property (readingData && pollingControlOut); // exercise override
  cover property (!pollingControlIn && !pollingControlOut);
  cover property ((!readingData && writingData) ##1 DataOutValid);

endmodule

bind Gateway Gateway_SVA SVA_GATEWAY();