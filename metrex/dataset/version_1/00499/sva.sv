// SVA for FSM. Bind this file to the DUT.
// Focus: reset behavior, ROM decode, pipeline alignment, arithmetic, outputs.

module FSM_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic [25:0] rom_q,
  input  logic [5:0]  ram_a_addr,
  input  logic [5:0]  ram_b_addr,
  input  logic        ram_b_w,
  input  logic [10:0] pe,
  input  logic        done,
  // internal regs
  input  logic [5:0]  dest,
  input  logic [1:0]  op,
  input  logic [5:0]  times,
  input  logic [5:0]  src1,
  input  logic [5:0]  src2,
  input  logic [10:0] result
);

  default clocking cb @(posedge clk); endclocking
  // Use disable iff for non-reset checks; use explicit reset-> zeros property separately.
  // ---------------------------------------------------------
  // Reset clears all architectural state
  // ---------------------------------------------------------
  assert property (@(posedge clk)
    reset |-> (dest==0 && op==0 && times==0 && src1==0 && src2==0 && result==0 &&
               ram_a_addr==0 && ram_b_addr==0 && ram_b_w==0 && pe==0 && done==0));

  // ---------------------------------------------------------
  // ROM decode into registers (same-cycle, post-edge)
  // ---------------------------------------------------------
  assert property (@(posedge clk) disable iff (reset)
    (dest==rom_q[25:20]) && (src1==rom_q[19:14]) && (op==rom_q[13:12]) &&
    (times==rom_q[11:6]) && (src2==rom_q[5:0]));

  // ---------------------------------------------------------
  // Address pipeline: 1-cycle from ROM decode to RAM A/B addresses
  // ---------------------------------------------------------
  assert property (@(posedge clk) disable iff (reset)
    (ram_a_addr == $past(rom_q[19:14])) && (ram_b_addr == $past(rom_q[5:0])));

  // ---------------------------------------------------------
  // ALU result based on previous-cycle operands/opcode
  // Width-accurate arithmetic and truncation
  // ---------------------------------------------------------
  assert property (@(posedge clk) disable iff (reset)
    result ==
      (($past(op)==2'b00) ? {5'b0, ( $past(src1) + $past(src2) )} :
       ($past(op)==2'b01) ? {5'b0, ( $past(src1) - $past(src2) )} :
       ($past(op)==2'b10) ? ( ( $past(src1)*$past(src1)*$past(src1)*$past(times) )[10:0] ) :
                            ( ( $past(src1)*$past(src2) )[10:0] )));

  // ---------------------------------------------------------
  // PE is 1-cycle behind result
  // ---------------------------------------------------------
  assert property (@(posedge clk) disable iff (reset)
    pe == $past(result));

  // Optional stronger check: PE matches ROM decode with 2-cycle latency
  assert property (@(posedge clk) disable iff (reset)
    pe ==
      (($past(op,2)==2'b00) ? {5'b0, ( $past(src1,2) + $past(src2,2) )} :
       ($past(op,2)==2'b01) ? {5'b0, ( $past(src1,2) - $past(src2,2) )} :
       ($past(op,2)==2'b10) ? ( ( $past(src1,2)*$past(src1,2)*$past(src1,2)*$past(times,2) )[10:0] ) :
                              ( ( $past(src1,2)*$past(src2,2) )[10:0] )));

  // ---------------------------------------------------------
  // done and ram_b_w are high whenever not in reset
  // ---------------------------------------------------------
  assert property (@(posedge clk) (done   == !reset));
  assert property (@(posedge clk) (ram_b_w== !reset));

  // ---------------------------------------------------------
  // Outputs are known when not in reset
  // ---------------------------------------------------------
  assert property (@(posedge clk) disable iff (reset)
    !$isunknown({ram_a_addr, ram_b_addr, ram_b_w, pe, done}));

  // ---------------------------------------------------------
  // Functional coverage
  // ---------------------------------------------------------
  cover property (@(posedge clk) disable iff (reset) op==2'b00);
  cover property (@(posedge clk) disable iff (reset) op==2'b01);
  cover property (@(posedge clk) disable iff (reset) op==2'b10);
  cover property (@(posedge clk) disable iff (reset) op==2'b11);

  // Subtraction underflow case (mod-64 behavior)
  cover property (@(posedge clk) disable iff (reset)
    ($past(op)==2'b01) && ($past(src1) < $past(src2)));

  // CUBIC overflow beyond 11 bits
  cover property (@(posedge clk) disable iff (reset)
    ($past(op)==2'b10) &&
    (|(( $past(src1)*$past(src1)*$past(src1)*$past(times) ) >> 11)));

endmodule

// Bind to DUT (connect to internal regs)
bind FSM FSM_sva u_FSM_sva (
  .clk(clk),
  .reset(reset),
  .rom_q(rom_q),
  .ram_a_addr(ram_a_addr),
  .ram_b_addr(ram_b_addr),
  .ram_b_w(ram_b_w),
  .pe(pe),
  .done(done),
  .dest(dest),
  .op(op),
  .times(times),
  .src1(src1),
  .src2(src2),
  .result(result)
);