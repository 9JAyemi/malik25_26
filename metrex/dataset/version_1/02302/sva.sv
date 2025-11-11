// SVA for eth_outputcontrol
// Bind into the DUT to access internal regs/wires
bind eth_outputcontrol eth_outputcontrol_sva sv_eth_outputcontrol_sva();

module eth_outputcontrol_sva;

  // Use DUT scope signals directly via bind
  // Clk, Reset, WriteOp, NoPre, InProgress, ShiftedBit, BitCounter, MdcEn_n
  // SerialEn, MdoEn_2d, MdoEn_d, MdoEn, Mdo_2d, Mdo_d, Mdo

  default clocking cb @(posedge Clk); endclocking
  default disable iff (Reset);

  // X/Z checks (disabled during Reset)
  a_no_x_inputs:  assert property (!Reset |-> !$isunknown({WriteOp,NoPre,InProgress,ShiftedBit,BitCounter,MdcEn_n}));
  a_no_x_outputs: assert property (!Reset |-> !$isunknown({SerialEn,MdoEn_2d,MdoEn_d,MdoEn,Mdo_2d,Mdo_d,Mdo}));

  // Combinational SerialEn definition equivalence
  a_serialen_def: assert property (
    SerialEn ==
      ( ( WriteOp & InProgress &
          ( (BitCounter > 7'd31) | ((BitCounter == 7'd0) & NoPre) )
        )
        |
        ( (~WriteOp) & InProgress &
          ( ((BitCounter > 7'd31) & (BitCounter < 7'd46)) | ((BitCounter == 7'd0) & NoPre) )
        )
      )
  );

  // SerialEn must be low when not InProgress
  a_serialen_inprog: assert property (!InProgress |-> !SerialEn);

  // Asynchronous reset clears regs immediately and holds while asserted
  a_rst_async: assert property (@(posedge Reset)
    (MdoEn_2d==1'b0 && MdoEn_d==1'b0 && MdoEn==1'b0 &&
     Mdo_2d==1'b0  && Mdo_d==1'b0  && Mdo==1'b0)
  );
  a_rst_hold:  assert property (@(posedge Clk) Reset |-> 
    (MdoEn_2d==1'b0 && MdoEn_d==1'b0 && MdoEn==1'b0 &&
     Mdo_2d==1'b0  && Mdo_d==1'b0  && Mdo==1'b0)
  );

  // Registers hold when MdcEn_n is low
  a_hold_regs: assert property (!MdcEn_n |-> $stable({MdoEn_2d,MdoEn_d,MdoEn,Mdo_2d,Mdo_d,Mdo}));

  // Update semantics on MdcEn_n (use !$past(Reset) to ensure $past is defined)
  a_mdoen_2d: assert property ( MdcEn_n |-> 
    MdoEn_2d == ( SerialEn | (InProgress & (BitCounter < 7'd32)) )
  );
  a_mdoen_d:  assert property ( (MdcEn_n && !$past(Reset)) |-> 
    MdoEn_d  == $past(MdoEn_2d)
  );
  a_mdoen:    assert property ( (MdcEn_n && !$past(Reset)) |-> 
    MdoEn    == $past(MdoEn_d)
  );

  a_mdo_2d:   assert property ( MdcEn_n |-> 
    Mdo_2d   == ( (~SerialEn) & (BitCounter < 7'd32) )
  );
  a_mdo_d:    assert property ( (MdcEn_n && !$past(Reset)) |-> 
    Mdo_d    == ( ShiftedBit | $past(Mdo_2d) )
  );
  a_mdo:      assert property ( (MdcEn_n && !$past(Reset)) |-> 
    Mdo      == $past(Mdo_d)
  );

  // Basic functional covers to hit key paths
  c_reset_release: cover property (Reset ##1 !Reset ##1 MdcEn_n);
  c_serial_write:  cover property (MdcEn_n && InProgress &&  WriteOp && (BitCounter > 7'd31) && SerialEn);
  c_serial_read:   cover property (MdcEn_n && InProgress && !WriteOp && (BitCounter > 7'd31) && (BitCounter < 7'd46) && SerialEn);
  c_nopre_path:    cover property (MdcEn_n && InProgress && (BitCounter==7'd0) && NoPre && SerialEn);
  c_preamble_drive:cover property (MdcEn_n && (BitCounter < 7'd32) && !SerialEn && Mdo_2d);
  c_mdo_toggle:    cover property (MdcEn_n ##1 MdcEn_n && $changed(Mdo));

endmodule