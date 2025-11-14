// SystemVerilog Assertions for top_module, mux_4to1, and shift_register
// Concise yet comprehensive checks and coverage

// Top-level SVA: cross-module checks and mux functional checks from top
module top_module_sva (
  input logic        CLK,
  input logic        RST,
  input logic        LD,
  input logic [3:0]  D,
  input logic [3:0]  in,
  input logic [1:0]  sel,
  input logic        enable,
  input logic [3:0]  OUT,
  input logic [3:0]  mux_out,
  input logic [3:0]  shift_reg_out
);
  default clocking cb @(posedge CLK); endclocking

  // OUT must be bitwise AND of mux_out and shift_reg_out
  a_out_and: assert property (OUT == (mux_out & shift_reg_out));

  // While in reset, shift_reg_out must be 0 and OUT must be 0
  a_rst_clears_q: assert property (RST |-> (shift_reg_out == 4'b0));
  a_rst_forces_out_zero: assert property (RST |-> (OUT == 4'b0));

  // Mux functional checks (as implemented in RTL)
  // enable=0 -> out = 0
  a_mux_disable_zero: assert property (!enable |-> (mux_out == 4'b0));

  // enable=1 and sel known -> out equals zero-extended selected input bit
  a_mux_select: assert property (
    enable && !$isunknown(sel) |-> (mux_out == {3'b000, in[sel]})
  );

  // No-X on mux_out when inputs are known
  a_mux_no_x: assert property (
    enable && !$isunknown({in,sel}) |-> !$isunknown(mux_out)
  );

  // Coverage
  c_out_nonzero: cover property (!RST && (OUT != 4'b0));
  c_mux_sel00:   cover property (enable && (sel==2'b00));
  c_mux_sel01:   cover property (enable && (sel==2'b01));
  c_mux_sel10:   cover property (enable && (sel==2'b10));
  c_mux_sel11:   cover property (enable && (sel==2'b11));
  c_mux_out1:    cover property (enable && (mux_out == 4'b0001));
  c_mux_out0:    cover property (!enable || (mux_out == 4'b0000));
endmodule

bind top_module top_module_sva u_top_module_sva (
  .CLK(CLK),
  .RST(RST),
  .LD(LD),
  .D(D),
  .in(in),
  .sel(sel),
  .enable(enable),
  .OUT(OUT),
  .mux_out(mux_out),
  .shift_reg_out(shift_reg_out)
);

// Shift-register SVA: exact sequential behavior, reset, load, rotate
module shift_register_sva (
  input logic        CLK,
  input logic        RST,
  input logic        LD,
  input logic [3:0]  D,
  input logic [3:0]  Q
);
  default clocking cb @(posedge CLK); endclocking

  // Asynchronous reset asserts Q==0 immediately and holds while RST=1
  a_async_rst_now: assert property (@(posedge RST) (Q == 4'b0));
  a_rst_holds_zero: assert property (RST |-> (Q == 4'b0));

  // Load on clock when not in reset
  a_load: assert property (disable iff (RST) LD |=> (Q == $past(D)));

  // Rotate-left by one when LD=0 (not in reset)
  a_rotate: assert property (
    disable iff (RST) !LD |=> (Q == {$past(Q[2:0]), $past(Q[3])})
  );

  // After 4 consecutive rotates (no loads), Q returns to its value 4 cycles ago
  a_full_cycle: assert property (
    disable iff (RST) (!LD)[*4] |=> (Q == $past(Q,4))
  );

  // Coverage
  c_rst:     cover property ($rose(RST));
  c_load:    cover property (disable iff (RST) LD);
  c_rotate:  cover property (disable iff (RST) !LD);
  c_cycle:   cover property (disable iff (RST) (!LD)[*4] ##1 (Q == $past(Q,4)));
endmodule

bind shift_register shift_register_sva u_shift_register_sva (
  .CLK(CLK),
  .RST(RST),
  .LD(LD),
  .D(D),
  .Q(Q)
);

// Optional: direct mux SVA (bound to mux_4to1) if you want localized checks too
module mux_4to1_sva (
  input logic [3:0] in,
  input logic [1:0] sel,
  input logic       enable,
  input logic [3:0] out
);
  // Sample on any value change via ##0 tick using an arbitrary clockless property context
  // Use simple concurrent assertions sampled continuously at time 0 steps
  a_mux_disable_zero: assert property (##0 (!enable) |-> (out == 4'b0));
  a_mux_select:       assert property (##0 (enable && !$isunknown(sel)) |-> (out == {3'b000, in[sel]}));
  a_no_x_out:         assert property (##0 (enable && !$isunknown({in,sel})) |-> !$isunknown(out));

  // Coverage
  c_sel00: cover property (##0 enable && (sel==2'b00));
  c_sel01: cover property (##0 enable && (sel==2'b01));
  c_sel10: cover property (##0 enable && (sel==2'b10));
  c_sel11: cover property (##0 enable && (sel==2'b11));
endmodule

bind mux_4to1 mux_4to1_sva u_mux_4to1_sva (
  .in(in),
  .sel(sel),
  .enable(enable),
  .out(out)
);