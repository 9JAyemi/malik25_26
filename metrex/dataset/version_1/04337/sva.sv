// SVA checker for top_module
module top_module_sva (
  input  logic        clk,
  input  logic        areset,
  input  logic        load,
  input  logic        ena,
  input  logic        A, B, SEL, DATA,
  input  logic        Y,
  input  logic [3:0]  Q,
  // internal DUT signals (connected via bind)
  input  logic [3:0]  shift_reg,
  input  logic        mux_out
);
  default clocking cb @(posedge clk); endclocking

  // Combinational mux correctness (and wire integrity)
  ap_mux:     assert property (Y == mux_out && mux_out == (SEL ? DATA : (A ^ B)));

  // Asynchronous reset must force zeros when sampled on clock
  ap_rst:     assert property (@(posedge clk) areset |-> (Q == 4'b0 && shift_reg == 4'b0));

  // When disabled, state holds
  ap_hold:    assert property (disable iff (areset)
                               !ena |=> (Q == $past(Q) && shift_reg == $past(shift_reg)));

  // Load behavior (note DATA is 1-bit; expect zero-extend)
  ap_load:    assert property (disable iff (areset)
                               (ena && load) |=> (Q == {3'b0, DATA} && shift_reg == {3'b0, DATA}));

  // Shift behavior as implemented (swap with truncation effect)
  ap_shift:   assert property (disable iff (areset)
                               (ena && !load) |=> (Q == $past(shift_reg) && shift_reg == $past(Q)));

  // No X/Z on key outputs after reset released
  ap_no_x:    assert property (disable iff (areset) !$isunknown({Q, shift_reg, Y}));

  // Coverage: reset, mux branches, and each datapath mode
  cp_rst:     cover  property (@(posedge clk) areset ##1 !areset);
  cp_mux0:    cover  property (!SEL && (Y == (A ^ B)));
  cp_mux1:    cover  property ( SEL && (Y == DATA));
  cp_load:    cover  property (disable iff (areset)
                               (ena && load) |=> (Q == {3'b0, DATA}));
  cp_shift:   cover  property (disable iff (areset)
                               (ena && !load) |=> (Q == $past(shift_reg)));
  cp_hold:    cover  property (disable iff (areset) !ena);
endmodule

// Bind into DUT, including internal nets
bind top_module top_module_sva u_top_module_sva (
  .clk(clk),
  .areset(areset),
  .load(load),
  .ena(ena),
  .A(A), .B(B), .SEL(SEL), .DATA(DATA),
  .Y(Y),
  .Q(Q),
  .shift_reg(shift_reg),
  .mux_out(mux_out)
);