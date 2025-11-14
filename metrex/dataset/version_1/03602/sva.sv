// SVA for Serial_in_parallel_out_enable_behavior
// Bind these checkers into the DUT

module siposeb_sva (
  input logic        Clk,
  input logic        reset,
  input logic        ShiftEn,
  input logic        ShiftIn,
  input logic        ShiftOut,
  input logic [3:0]  ParallelOut,
  input logic [15:0] ShiftReg,
  input logic [3:0]  ParallelReg
);
  default clocking cb @(posedge Clk); endclocking

  // Reset behavior (sync): next cycle after reset high, regs/outs are zero
  assert property (reset |=> (ShiftReg==16'h0 && ParallelReg==4'h0));
  assert property (reset |=> (ShiftOut==1'b0 && ParallelOut==4'h0));

  // Outputs mirror internals every cycle
  assert property (ParallelOut == ParallelReg);
  assert property (ShiftOut == ShiftReg[15]);

  // Shift register functional update when enabled
  assert property (disable iff (reset)
                   ShiftEn |=> ShiftReg == { $past(ShiftReg,1,reset)[14:0], $past(ShiftIn,1,reset) });

  // Hold behavior when not enabled
  assert property (disable iff (reset)
                   !ShiftEn |=> (ShiftReg == $past(ShiftReg,1,reset) && ParallelReg == $past(ParallelReg,1,reset)));

  // ParallelReg update behavior (note: 1-bit LSB of each nibble captured by RTL)
  assert property (disable iff (reset)
                   ShiftEn |=> (ParallelReg[0] == $past(ShiftReg[0],1,reset)  &&
                                ParallelReg[1] == $past(ShiftReg[4],1,reset)  &&
                                ParallelReg[2] == $past(ShiftReg[8],1,reset)  &&
                                ParallelReg[3] == $past(ShiftReg[12],1,reset)));

  // No spurious updates without enable (excluding reset)
  assert property (disable iff (reset) $changed(ShiftReg)  |-> $past(ShiftEn,1,reset));
  assert property (disable iff (reset) $changed(ParallelReg) |-> $past(ShiftEn,1,reset));

  // No X/Z after reset deasserted
  assert property (disable iff (reset) !$isunknown({ShiftReg, ParallelReg, ShiftOut, ParallelOut}));

  // Coverage
  cover property (disable iff (reset) ShiftEn && (ShiftIn==1'b0));
  cover property (disable iff (reset) ShiftEn && (ShiftIn==1'b1));
  cover property (disable iff (reset) !ShiftEn && $stable({ShiftReg, ParallelReg}));

  // Observe that a '1' shifted in reaches MSB after 16 enabled shifts
  cover property (disable iff (reset)
                  (ShiftEn && ShiftIn) ##1 (ShiftEn)[*15] ##0 (ShiftOut));

  // Each ParallelReg bit changes at least once
  genvar i;
  generate for (i=0;i<4;i++) begin : gen_cov_pr
    cover property (disable iff (reset) $changed(ParallelReg[i]));
  end endgenerate
endmodule

bind Serial_in_parallel_out_enable_behavior
  siposeb_sva u_siposeb_sva (
    .Clk(Clk),
    .reset(reset),
    .ShiftEn(ShiftEn),
    .ShiftIn(ShiftIn),
    .ShiftOut(ShiftOut),
    .ParallelOut(ParallelOut),
    .ShiftReg(ShiftReg),
    .ParallelReg(ParallelReg)
  );