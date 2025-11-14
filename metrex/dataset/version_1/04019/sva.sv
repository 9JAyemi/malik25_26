// SVA for eth_shiftreg
// Bind this file to the DUT: bind eth_shiftreg eth_shiftreg_sva sva();

module eth_shiftreg_sva (eth_shiftreg dut);

  default clocking cb @(posedge dut.Clk); endclocking
  default disable iff (dut.Reset);

  // Basic combinational relation
  assert property (dut.ShiftedBit == dut.ShiftReg[7]);

  // Asynchronous reset values observed on next clk
  assert property (@(posedge dut.Clk)
                   dut.Reset |-> (dut.ShiftReg==8'h00 && dut.Prsd==16'h0000 && dut.LinkFail==1'b0));

  // Hold when MdcEn_n deasserted
  assert property (!dut.MdcEn_n |=> $stable({dut.ShiftReg, dut.Prsd, dut.LinkFail}));

  // ByteSelect loads
  assert property (dut.MdcEn_n && dut.ByteSelect==4'h1
                   |=> dut.ShiftReg == {2'b01, ~$past(dut.WriteOp), $past(dut.WriteOp), $past(dut.Fiad[4:1])});

  assert property (dut.MdcEn_n && dut.ByteSelect==4'h2
                   |=> dut.ShiftReg == {$past(dut.Fiad[0]), $past(dut.Rgad[4:0]), 2'b10});

  assert property (dut.MdcEn_n && dut.ByteSelect==4'h4
                   |=> dut.ShiftReg == $past(dut.CtrlData[15:8]));

  assert property (dut.MdcEn_n && dut.ByteSelect==4'h8
                   |=> dut.ShiftReg == $past(dut.CtrlData[7:0]));

  // Default case for any other nonzero ByteSelect
  assert property (dut.MdcEn_n && (dut.ByteSelect!=4'h0) && !(dut.ByteSelect inside {4'h1,4'h2,4'h4,4'h8})
                   |=> dut.ShiftReg == 8'h00);

  // Shift operation when no ByteSelect
  assert property (dut.MdcEn_n && dut.ByteSelect==4'h0
                   |=> dut.ShiftReg == { $past(dut.ShiftReg[6:0]), $past(dut.Mdi) });

  // PRSD low byte update
  assert property (dut.MdcEn_n && dut.ByteSelect==4'h0 && dut.LatchByte[0]
                   |=> dut.Prsd[7:0] == { $past(dut.ShiftReg[6:0]), $past(dut.Mdi) });

  // PRSD high byte update (only when LB[0]==0)
  assert property (dut.MdcEn_n && dut.ByteSelect==4'h0 && !dut.LatchByte[0] && dut.LatchByte[1]
                   |=> dut.Prsd[15:8] == { $past(dut.ShiftReg[6:0]), $past(dut.Mdi) });

  // PRSD stability guards
  assert property (dut.MdcEn_n && dut.ByteSelect==4'h0 && !dut.LatchByte[0]
                   |=> $stable(dut.Prsd[7:0]));
  assert property (dut.MdcEn_n && dut.ByteSelect==4'h0 && dut.LatchByte[0]
                   |=> $stable(dut.Prsd[15:8]));

  // LinkFail update and hold
  assert property (dut.MdcEn_n && dut.ByteSelect==4'h0 && dut.LatchByte[0] && (dut.Rgad==5'h01)
                   |=> dut.LinkFail == ~ $past(dut.ShiftReg[1]));
  assert property (!(dut.MdcEn_n && dut.ByteSelect==4'h0 && dut.LatchByte[0] && (dut.Rgad==5'h01))
                   |=> $stable(dut.LinkFail));

  // Coverage
  cover property (dut.Reset ##1 !dut.Reset);
  cover property (dut.MdcEn_n && dut.ByteSelect==4'h0);                 // shift path
  cover property (dut.MdcEn_n && dut.ByteSelect==4'h1);
  cover property (dut.MdcEn_n && dut.ByteSelect==4'h2);
  cover property (dut.MdcEn_n && dut.ByteSelect==4'h4);
  cover property (dut.MdcEn_n && dut.ByteSelect==4'h8);
  cover property (dut.MdcEn_n && (dut.ByteSelect!=4'h0) &&
                  !(dut.ByteSelect inside {4'h1,4'h2,4'h4,4'h8}));       // default case
  cover property (dut.MdcEn_n && dut.ByteSelect==4'h0 && dut.LatchByte[0]);
  cover property (dut.MdcEn_n && dut.ByteSelect==4'h0 && !dut.LatchByte[0] && dut.LatchByte[1]);
  cover property (dut.MdcEn_n && dut.ByteSelect==4'h0 && (dut.LatchByte==2'b11)); // precedence on LB[0]
  cover property (!dut.MdcEn_n ##1 $stable({dut.ShiftReg, dut.Prsd, dut.LinkFail}));

endmodule

bind eth_shiftreg eth_shiftreg_sva sva();