// SVA for eth_outputcontrol
// Focus: reset behavior, MdcEn_n gating, pipeline correctness, SerialEn definition, X-checks, key coverage.

module eth_outputcontrol_sva;

  default clocking cb @(posedge Clk); endclocking

  // Reset clears and holds zeros
  assert property (Reset |=> (MdoEn_2d==0 && MdoEn_d==0 && MdoEn==0 && Mdo_2d==0 && Mdo_d==0 && Mdo==0));
  assert property (Reset |=> $stable({MdoEn_2d,MdoEn_d,MdoEn,Mdo_2d,Mdo_d,Mdo}));

  // Hold when MdcEn_n is low
  assert property (!Reset && !MdcEn_n |=> $stable({MdoEn_2d,MdoEn_d,MdoEn,Mdo_2d,Mdo_d,Mdo}));

  // Update equations when MdcEn_n is high (next-cycle equality to current RHS)
  assert property (!Reset && MdcEn_n |=> MdoEn_2d == $past( SerialEn | (InProgress && (BitCounter<7'd32)) ));
  assert property (!Reset && MdcEn_n |=> MdoEn_d  == $past(MdoEn_2d));
  assert property (!Reset && MdcEn_n |=> MdoEn    == $past(MdoEn_d));

  assert property (!Reset && MdcEn_n |=> Mdo_2d == $past((!SerialEn) && (BitCounter<7'd32)));
  assert property (!Reset && MdcEn_n |=> Mdo_d  == ($past(ShiftedBit) || $past(Mdo_2d)));
  assert property (!Reset && MdcEn_n |=> Mdo    == $past(Mdo_d));

  // SerialEn definition and sanity
  assert property (SerialEn ==
                   ( (WriteOp && InProgress && ((BitCounter>7'd31) || ((BitCounter==7'd0) && NoPre))) ||
                     ((!WriteOp) && InProgress && (((BitCounter>7'd31) && (BitCounter<7'd46)) || ((BitCounter==7'd0) && NoPre)))) ));
  assert property (!InProgress |-> !SerialEn);

  // No X on outputs in normal operation
  assert property (!Reset |-> !$isunknown({MdoEn,Mdo}));

  // Key coverage
  cover property (!Reset && MdcEn_n && InProgress && !WriteOp && (BitCounter>7'd31) && (BitCounter<7'd46) && SerialEn); // read serialize window
  cover property (!Reset && MdcEn_n && InProgress &&  WriteOp && (BitCounter>7'd31) && SerialEn);                       // write serialize window
  cover property (!Reset && MdcEn_n && InProgress && (BitCounter<7'd32) && !SerialEn);                                   // preamble ones
  cover property (!Reset && MdcEn_n && (BitCounter==7'd0) && NoPre && SerialEn);                                         // no-preamble start
  cover property (Reset ##1 !Reset);                                                                                     // reset release

endmodule

bind eth_outputcontrol eth_outputcontrol_sva sva_inst();