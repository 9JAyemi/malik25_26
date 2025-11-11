// SVA package for fifo_buffer and fifo_bt_txd_synchronizer_ff
// Focused, high-quality checks and minimal but meaningful coverage.

`ifndef FIFO_BUFFER_SVA
`define FIFO_BUFFER_SVA

// Assertions for top fifo_buffer
module fifo_buffer_sva (
  input logic         rd_clk,
  input logic         g7serrst0,
  input logic         in0,
  input logic         in0_sync,           // internal wire in fifo_buffer
  input logic         Q_reg,              // internal reg in fifo_buffer
  input logic         rd_rst_asreg_reg,   // internal reg in fifo_buffer
  input logic         out
);
  default clocking cb @(posedge rd_clk); endclocking

  // Asynchronous reset drives internal regs low immediately; at any sampled clk while low, they must be 0
  // Also out must read as 0 on any clock while reset is low
  assert property (@(negedge g7serrst0) 1 |-> (Q_reg==0 && rd_rst_asreg_reg==0))
    else $error("fifo_buffer: async reset did not clear Q_reg/rd_rst_asreg_reg");
  assert property (cb !g7serrst0 |-> (Q_reg==0 && rd_rst_asreg_reg==0 && out==0))
    else $error("fifo_buffer: state not held at 0 while g7serrst0=0");

  // Sequential relationships (when not under async reset)
  assert property (cb g7serrst0 |-> (out == $past(Q_reg)))
    else $error("fifo_buffer: out != $past(Q_reg)");
  assert property (cb g7serrst0 |-> (Q_reg == $past(in0_sync)))
    else $error("fifo_buffer: Q_reg != $past(in0_sync)");
  assert property (cb g7serrst0 |-> (rd_rst_asreg_reg == (~$past(Q_reg) & $past(in0_sync))))
    else $error("fifo_buffer: rd_rst_asreg_reg not generated as ~Q_reg & in0_sync (past)");

  // No-X while out of reset
  assert property (cb g7serrst0 |-> !$isunknown({Q_reg, rd_rst_asreg_reg, out}))
    else $error("fifo_buffer: X/Z detected out of reset");

  // Minimal but meaningful coverage
  cover property (cb $fell(g7serrst0) ##1 $rose(g7serrst0));
  // Rising on in0 propagates to out after 5 cycles when resets are high
  cover property (cb (g7serrst0 && rd_rst_asreg_reg && $rose(in0)) ##5 $rose(out));
endmodule

// Assertions for fifo_bt_txd_synchronizer_ff
module fifo_bt_txd_synchronizer_ff_sva (
  input logic rd_clk,
  input logic rd_rst_asreg_reg, // active-low async reset
  input logic in0,
  input logic in0_sync,         // internal reg in synchronizer
  input logic Q_reg,            // internal reg in synchronizer
  input logic out
);
  default clocking cb @(posedge rd_clk); endclocking

  // Async reset clears Q_reg immediately; on any clk while reset low, Q_reg must be 0
  assert property (@(negedge rd_rst_asreg_reg) 1 |-> (Q_reg==0))
    else $error("sync: async reset did not clear Q_reg");
  assert property (cb !rd_rst_asreg_reg |-> (Q_reg==0))
    else $error("sync: Q_reg not held at 0 while rd_rst_asreg_reg=0");

  // 1-cycle staging of in0
  assert property (cb in0_sync == $past(in0))
    else $error("sync: in0_sync != $past(in0)");

  // Q_reg captures in0_sync when not in reset; else held at 0
  assert property (cb rd_rst_asreg_reg |-> (Q_reg == $past(in0_sync)))
    else $error("sync: Q_reg != $past(in0_sync) when not in reset");

  // out follows Q_reg by 1 cycle
  assert property (cb out == $past(Q_reg))
    else $error("sync: out != $past(Q_reg)");

  // No-X while out of reset
  assert property (cb rd_rst_asreg_reg |-> !$isunknown({in0_sync, Q_reg, out}))
    else $error("sync: X/Z detected out of reset");

  // Coverage: reset pulse and data propagation through the 2-stage sync
  cover property (cb $fell(rd_rst_asreg_reg) ##1 $rose(rd_rst_asreg_reg));
  cover property (cb (rd_rst_asreg_reg && $rose(in0)) ##2 $rose(out));
endmodule

// Bind into DUT
bind fifo_buffer                      fifo_buffer_sva               u_fifo_buffer_sva       (
  .rd_clk(rd_clk),
  .g7serrst0(g7serrst[0]),
  .in0(in0),
  .in0_sync(in0_sync),
  .Q_reg(Q_reg),
  .rd_rst_asreg_reg(rd_rst_asreg_reg),
  .out(out)
);

bind fifo_bt_txd_synchronizer_ff      fifo_bt_txd_synchronizer_ff_sva u_sync_sva            (
  .rd_clk(rd_clk),
  .rd_rst_asreg_reg(rd_rst_asreg_reg),
  .in0(in0),
  .in0_sync(in0_sync),
  .Q_reg(Q_reg),
  .out(out)
);

`endif