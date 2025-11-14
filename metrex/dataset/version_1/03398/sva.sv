// SVA for k580wm80a
// Bind this module or paste into a separate SVA file and bind to the DUT.

module k580wm80a_sva (k580wm80a dut);

  default clocking cb @(posedge dut.clk); endclocking
  default disable iff (dut.reset);

  // Convenience reductions
  wire [10:0] mgrp = {
    dut.M16|dut.M17,  // 10
    dut.M14|dut.M15,  // 9
    dut.M12|dut.M13,  // 8
    dut.M10|dut.M11,  // 7
    dut.M8 |dut.M9,   // 6
    dut.M7,           // 5
    dut.M6,           // 4
    dut.M5,           // 3
    dut.M4,           // 2
    dut.M2 |dut.M3,   // 1
    dut.M1            // 0
  };

  // Reset puts design into known state (checked on next clk after reset rise)
  assert property (@(posedge dut.clk)
    $rose(dut.reset) |=> (
      dut.state==3'b000 &&
      {dut.M1,dut.M2,dut.M3,dut.M4,dut.M5,dut.M6,dut.M7,
       dut.M8,dut.M9,dut.M10,dut.M11,dut.M12,dut.M13,dut.M14,dut.M15,dut.M16,dut.M17} == 17'b0 &&
      dut.PC==16'b0 && dut.SP==16'b0 &&
      {dut.FS,dut.FZ,dut.FA,dut.FP,dut.FC}==5'b0 &&
      dut.addr==16'b0 && dut.odata==8'b0 &&
      dut.sync==1'b0 && dut.rd_==1'b0 && dut.wr==1'b0 &&
      {dut.jmp,dut.halt,dut.save_alu,dut.save_a,dut.save_r,dut.save_rp,
       dut.incdec,dut.intproc}==8'b0 && dut.inte==2'b0
    )
  );

  // When ce==0, architectural state holds
  assert property (!dut.ce |-> $stable({
    dut.state,
    dut.M1,dut.M2,dut.M3,dut.M4,dut.M5,dut.M6,dut.M7,
    dut.M8,dut.M9,dut.M10,dut.M11,dut.M12,dut.M13,dut.M14,dut.M15,dut.M16,dut.M17,
    dut.PC,dut.SP,
    dut.A,dut.B,dut.C,dut.D,dut.E,dut.H,dut.L,
    dut.FS,dut.FZ,dut.FA,dut.FP,dut.FC,
    dut.rd_,dut.wr,dut.sync,
    dut.intproc,dut.addr,dut.odata
  }));

  // Machine-cycle group onehot0 (at most one active group at a time)
  assert property ($onehot0(mgrp));

  // Sync only in state 000; sync bus LSB always carries intproc
  assert property (dut.sync |-> dut.state==3'b000);
  assert property (dut.sync |-> dut.odata[0] == dut.intproc);

  // rd/inta derivations and mutual exclusion with wr
  assert property (dut.rd   == (dut.rd_ & ~dut.intproc));
  assert property (dut.inta == (dut.rd_ &  dut.intproc));
  assert property (!(dut.wr && (dut.rd || dut.inta)));
  assert property (!(dut.rd && dut.inta)));

  // rd/wr happen only in state 001 and in the right cycle families
  assert property (dut.rd |-> (dut.state==3'b001) &&
                   (dut.M1 || dut.M2 || dut.M3 || dut.M4 || dut.M6 || dut.M8 || dut.M9 || dut.M12 || dut.M13));

  assert property (dut.wr |-> (dut.state==3'b001) &&
                   (dut.M5 || dut.M7 || dut.M10 || dut.M11 || dut.M14 || dut.M15));

  // PC update on instruction/opcode/data fetch steps (M1 and M2/M3 paths)
  assert property ((dut.state==3'b001 && dut.rd && dut.M1) |-> dut.PC == $past(dut.addr) + ($past(dut.intproc) ? 16'd0 : 16'd1));
  assert property ((dut.state==3'b001 && dut.rd && (dut.M2 || dut.M3)) |-> dut.PC == $past(dut.addr) + ($past(dut.intproc) ? 16'd0 : 16'd1));

  // Save-ALU updates flags and (usually) A as specified
  assert property (dut.ce && dut.state==3'b000 && dut.save_alu |=> (
      dut.FS == $past(dut.ALU[8]) &&
      dut.FZ == ~|$past(dut.ALU[8:1]) &&
      dut.FA == ($past(dut.ALU[5]) ^ $past(dut.ALUb4)) &&
      dut.FP == ~^$past(dut.ALU[8:1]) &&
      dut.FC == ($past(dut.ALU[9]) | ($past(dut.FC) & $past(dut.daa))) &&
      (($past(dut.IR[5:3])==3'b111) || (dut.A == $past(dut.ALU[8:1])))
  ));

  // save_a writes A with Z1
  assert property (dut.ce && dut.state==3'b000 && dut.save_a |=> dut.A == $past(dut.Z1));

  // save_r writes selected register with Z1
  assert property (dut.ce && dut.state==3'b000 && dut.save_r && $past(dut.IR[5:3])==3'b000 |=> dut.B == $past(dut.Z1));
  assert property (dut.ce && dut.state==3'b000 && dut.save_r && $past(dut.IR[5:3])==3'b001 |=> dut.C == $past(dut.Z1));
  assert property (dut.ce && dut.state==3'b000 && dut.save_r && $past(dut.IR[5:3])==3'b010 |=> dut.D == $past(dut.Z1));
  assert property (dut.ce && dut.state==3'b000 && dut.save_r && $past(dut.IR[5:3])==3'b011 |=> dut.E == $past(dut.Z1));
  assert property (dut.ce && dut.state==3'b000 && dut.save_r && $past(dut.IR[5:3])==3'b100 |=> dut.H == $past(dut.Z1));
  assert property (dut.ce && dut.state==3'b000 && dut.save_r && $past(dut.IR[5:3])==3'b101 |=> dut.L == $past(dut.Z1));
  assert property (dut.ce && dut.state==3'b000 && dut.save_r && $past(dut.IR[5:3])==3'b111 |=> dut.A == $past(dut.Z1));

  // inc/dec side-effects on flags when save_r with incdec
  assert property (dut.ce && dut.state==3'b000 && dut.save_r && $past(dut.incdec) |=> (
      dut.FS == $past(dut.Z1[7]) &&
      dut.FZ == ~|$past(dut.Z1) &&
      dut.FA == ($past(dut.IR[0]) ? ($past(dut.Z1[3:0]) != 4'hF) : ($past(dut.Z1[3:0]) == 4'h0)) &&
      dut.FP == ~^$past(dut.Z1)
  ));

  // save_rp writes selected register pair or SP/AF from WZ1
  assert property (dut.ce && dut.state==3'b000 && dut.save_rp && $past(dut.IR[5:4])==2'b00 |=> {dut.B,dut.C} == $past(dut.WZ1));
  assert property (dut.ce && dut.state==3'b000 && dut.save_rp && $past(dut.IR[5:4])==2'b01 |=> {dut.D,dut.E} == $past(dut.WZ1));
  assert property (dut.ce && dut.state==3'b000 && dut.save_rp && $past(dut.IR[5:4])==2'b10 |=> {dut.H,dut.L} == $past(dut.WZ1));
  assert property (dut.ce && dut.state==3'b000 && dut.save_rp && $past(dut.IR[5:4])==2'b11 |=> (
      ($past(dut.sphl) || !$past(dut.IR[7])) ?
          (dut.SP == $past(dut.WZ1)) :
          ({dut.A,dut.FS,dut.FZ,dut.FA,dut.FP,dut.FC} ==
            {$past(dut.WZ1[15:8]),$past(dut.WZ1[7]),$past(dut.WZ1[6]),$past(dut.WZ1[4]),$past(dut.WZ1[2]),$past(dut.WZ1[0])})
  ));

  // M5 (write through HL) protocol: address and data
  assert property (dut.M5 && dut.state==3'b000 |-> dut.sync && dut.addr=={dut.H,dut.L});
  assert property ($rose(dut.M5) ##1 dut.state==3'b001 |-> dut.wr && dut.odata == $past(dut.Z1));

  // IO read/write cycles addressing (M6/M7) use {Z,Z} and align rd/wr
  assert property (dut.M6 && dut.state==3'b000 |-> dut.addr == {dut.Z,dut.Z});
  assert property (dut.M7 && dut.state==3'b000 |-> dut.addr == {dut.Z,dut.Z});
  assert property (dut.M6 && dut.state==3'b001 |-> dut.rd);
  assert property (dut.M7 && dut.state==3'b001 |-> dut.wr);

  // Stack pop (M8/M9) and push (M10/M11) are read/write cycles with SP adjustment guarded in state 001
  assert property ((dut.M8 || dut.M9) && dut.state==3'b001 |-> dut.rd);
  assert property ((dut.M10 || dut.M11) && dut.state==3'b001 |-> dut.wr);

  // Coverage: exercise key cycles and features
  cover property (dut.sync && dut.M1 && dut.rd);                         // instruction fetch
  cover property (dut.M4 && dut.state==3'b001 && dut.rd);                // memory read (HL)
  cover property (dut.M5 && dut.state==3'b001 && dut.wr);                // memory write (HL)
  cover property (dut.M6 && dut.state==3'b001 && dut.rd);                // IO read
  cover property (dut.M7 && dut.state==3'b001 && dut.wr);                // IO write
  cover property ((dut.M8||dut.M9) && dut.state==3'b001 && dut.rd);      // stack pop
  cover property ((dut.M10||dut.M11) && dut.state==3'b001 && dut.wr);    // stack push
  cover property (dut.M16 && dut.state==3'b000);                         // 16-bit ADD start
  cover property (dut.inta && dut.rd);                                   // interrupt acknowledge
  cover property (dut.halt && dut.sync && dut.odata==8'b10001010);       // HALT status
  cover property (dut.save_alu);                                          // ALU update
  cover property (dut.save_r && dut.incdec);                              // INC/DEC with flags
  cover property (dut.save_rp && dut.IR[5:4]==2'b11 && dut.sphl);         // SP<=HL path
  cover property (dut.xthl && (dut.M10||dut.M11) && (dut.M8||dut.M9));    // XTHL activity window

endmodule

bind k580wm80a k580wm80a_sva sva_inst(.dut(this));