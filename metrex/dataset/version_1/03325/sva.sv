// SVA for cp0
`ifndef SR
`define SR    5'd12
`define CAUSE 5'd13
`define EPC   5'd14
`define PRID  5'd15
`endif

module cp0_sva;
  default clocking cb @(posedge clk); endclocking

  // Reset values (checked one cycle after rst assertion)
  assert property (@(posedge clk) rst |=> (ie==1'b1 && im==6'b110000 && exl==1'b0 && hwint_pend==6'b0 && PrId==32'h12345678));

  // Interrupt request definition
  assert property (@(posedge clk) disable iff (rst)
    IntReq == (ie && !exl && (|(hwint_pend & im)))
  );

  // hwint_pend must track HWInt each cycle
  assert property (@(posedge clk) disable iff (rst)
    1'b1 |=> (hwint_pend == $past(HWInt))
  );

  // On interrupt: capture EPC=pc-4, EXL=1, and ExcCode
  assert property (@(posedge clk) disable iff (rst)
    IntReq |=> (exl && _epc == ($past(pc)-32'd4) && _exccode == $past(ExcCode))
  );

  // SR write semantics
  assert property (@(posedge clk) disable iff (rst)
    (we && a2==`SR) |=> (im==$past(din[15:10]) &&
                         ie==$past(din[0]) &&
                         exl==($past(EXLClr) ? 1'b1 : $past(din[1])))
  );

  // EPC write semantics (writes current pc, not din)
  assert property (@(posedge clk) disable iff (rst)
    (we && a2==`EPC) |=> (_epc == $past(pc))
  );

  // EXLSet/EXLClr effects when not writing SR/EPC and no higher-priority IntReq
  assert property (@(posedge clk) disable iff (rst)
    (we && a2!=`SR && a2!=`EPC && EXLSet) |=> exl
  );
  assert property (@(posedge clk) disable iff (rst)
    (we && a2!=`SR && a2!=`EPC && !EXLSet && EXLClr) |=> !exl
  );
  assert property (@(posedge clk) disable iff (rst)
    (!we && !IntReq && EXLSet) |=> exl
  );
  assert property (@(posedge clk) disable iff (rst)
    (!we && !IntReq && !EXLSet && EXLClr) |=> !exl
  );

  // exl/ie must block IntReq
  assert property (@(posedge clk) disable iff (rst) exl  |-> !IntReq);
  assert property (@(posedge clk) disable iff (rst) !ie  |-> !IntReq);

  // dout mapping
  assert property (@(posedge clk) disable iff (rst)
    (a1==`SR) |-> (dout == {16'b0, im, 8'b0, exl, ie})
  );
  assert property (@(posedge clk) disable iff (rst)
    (a1==`CAUSE) |-> (dout[31:16]==16'b0 &&
                      dout[15:10]==hwint_pend &&
                      dout[9:7]==3'b0 &&
                      dout[6:2]==_exccode &&
                      dout[1:0]==2'b00)
  );
  assert property (@(posedge clk) disable iff (rst)
    (a1==`EPC)  |-> (dout == _epc)
  );
  assert property (@(posedge clk) disable iff (rst)
    (a1==`PRID) |-> (dout == PrId)
  );
  assert property (@(posedge clk) disable iff (rst)
    (a1!=`SR && a1!=`CAUSE && a1!=`EPC && a1!=`PRID) |-> (dout==32'h0000_0000)
  );

  // EPC output mirrors internal register
  assert property (@(posedge clk) disable iff (rst) EPC == _epc);

  // Coverage
  cover property (@(posedge clk) disable iff (rst) IntReq);
  cover property (@(posedge clk) disable iff (rst) IntReq |=> (exl && _epc==($past(pc)-32'd4)));
  cover property (@(posedge clk) disable iff (rst) (we && a2==`SR));
  cover property (@(posedge clk) disable iff (rst) (we && a2==`EPC));
  cover property (@(posedge clk) disable iff (rst) EXLSet);
  cover property (@(posedge clk) disable iff (rst) EXLClr);
  cover property (@(posedge clk) disable iff (rst) (a1==`CAUSE));
  cover property (@(posedge clk) disable iff (rst) (a1==`EPC));
  cover property (@(posedge clk) disable iff (rst) (a1==`PRID));
endmodule

bind cp0 cp0_sva cp0_sva_i();