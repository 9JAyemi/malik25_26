// SVA for shift_register_ring_counter
module shift_register_ring_counter (input clk, input d, output reg q);

  reg [2:0] shift_reg;

  always @(posedge clk)
    shift_reg <= {shift_reg[1:0], d};

  always @*
    q = shift_reg[2];

`ifndef SYNTHESIS
  // Environment: no X/Z on input d
  assume property (@(posedge clk) !$isunknown(d));

  // 1-cycle shift behavior
  assert property (@(posedge clk)
    !$isunknown({$past(shift_reg), $past(d)}) |-> shift_reg == {$past(shift_reg[1:0]), $past(d)}
  );

  // q mirrors MSB of shift_reg
  assert property (@(posedge clk)
    !$isunknown(shift_reg[2]) |-> q == shift_reg[2]
  );

  // End-to-end: q equals d from 3 cycles ago
  assert property (@(posedge clk)
    !$isunknown($past(d,3)) |-> q == $past(d,3)
  );

  // After pipeline fill, no X/Z in state or output
  assert property (@(posedge clk)
    $past(1'b1,3) |-> !$isunknown({shift_reg, q})
  );

  // Functional coverage: both values propagate through the 3-stage pipeline
  cover property (@(posedge clk) d==1 ##3 q==1);
  cover property (@(posedge clk) d==0 ##3 q==0);

  // Cover all 3-bit internal states
  generate
    genvar i;
    for (i=0; i<8; i++) begin : C_STATES
      cover property (@(posedge clk) shift_reg == i[2:0]);
    end
  endgenerate
`endif

endmodule