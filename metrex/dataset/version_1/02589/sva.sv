// SVA bind file for divide_by12
// Focused, high-quality checks and coverage for a combinational divider-by-12

bind divide_by12 divide_by12_sva u_divide_by12_sva(.*);

module divide_by12_sva (divide_by12 dut);

  // Golden functional equivalence: q = numer/12, r = numer%12
  assert property (@(dut.numer)
    !($isunknown(dut.numer))
    |-> (dut.quotient == (dut.numer/6'd12)) && (dut.remain == (dut.numer%6'd12))
  ) else $error("DIV12 mismatch: numer=%0d q=%0d r=%0d", dut.numer, dut.quotient, dut.remain);

  // Identity: numer = 12*q + r
  assert property (@(dut.numer)
    !($isunknown(dut.numer))
    |-> (dut.remain == (dut.numer - (6'd12 * dut.quotient))[3:0])
  );

  // Range checks
  assert property (@(dut.numer)
    !($isunknown(dut.numer))
    |-> (dut.quotient inside {[3'd0:3'd5]}) && (dut.remain inside {[4'd0:4'd11]})
  );

  // Structural checks implied by the implementation
  // Low 2 bits of remainder are a passthrough of numer[1:0]
  assert property (@(dut.numer)
    !($isunknown(dut.numer))
    |-> (dut.remain[1:0] == dut.numer[1:0])
  );

  // High 2 bits of remainder equal (numer[5:2] % 3)
  assert property (@(dut.numer)
    !($isunknown(dut.numer))
    |-> (dut.remain[3:2] == ( (dut.numer[5:2] % 3) [1:0] ))
  );

  // Internal defensive checks (since bind can see internals)
  // remain_bit3_bit2 must only take values 0..2
  assert property (@(dut.numer)
    !($isunknown(dut.numer[5:2]))
    |-> (dut.remain_bit3_bit2 inside {[4'd0:4'd2]})
  );

  // The truncation in the assign shall not corrupt high remainder bits
  assert property (@(dut.numer)
    !($isunknown(dut.numer))
    |-> (dut.remain[3:2] == dut.remain_bit3_bit2[1:0])
  );

  // X-propagation hygiene: known input -> known outputs
  assert property (@(dut.numer)
    !($isunknown(dut.numer))
    |-> !($isunknown({dut.quotient,dut.remain}))
  );

  // Concise but full functional coverage
  genvar i;

  // Cover all quotient values (0..5)
  for (i = 0; i < 6; i++) begin : COV_Q
    cover property (@(dut.numer) !($isunknown(dut.numer)) && (dut.quotient == i));
  end

  // Cover all remainder values (0..11)
  for (i = 0; i < 12; i++) begin : COV_R
    cover property (@(dut.numer) !($isunknown(dut.numer)) && (dut.remain == i));
  end

  // Cover passthrough of low 2 bits and mod-3 of high 4 bits
  for (i = 0; i < 4; i++) begin : COV_LOW2
    cover property (@(dut.numer) !($isunknown(dut.numer)) && (dut.numer[1:0] == i));
  end

  for (i = 0; i < 3; i++) begin : COV_HI_MOD3
    cover property (@(dut.numer) !($isunknown(dut.numer)) && ((dut.numer[5:2] % 3) == i));
  end

endmodule