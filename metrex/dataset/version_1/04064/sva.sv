// SVA for ac97_rst
`include "ac97_defines.v"

`ifndef AC97_RST_SVA
`define AC97_RST_SVA

module ac97_rst_sva (
  input  logic        clk,
  input  logic        rst,         // async, active-low
  input  logic        rst_force,
  input  logic        ps_ce,
  input  logic        ac97_rst_,
  input  logic [2:0]  cnt,
  input  logic        ce,
  input  logic        to,
  input  logic [5:0]  ps_cnt
);
  localparam int RST_DEL  = `AC97_RST_DEL;
  localparam int PS_TICKS = `AC97_250_PS;

  // Default clocking
  default clocking cb @(posedge clk); endclocking

  // Asynchronous reset takes effect immediately
  assert property (@(negedge rst) (ac97_rst_==1'b0 && cnt==3'd0 && ps_cnt==6'd0))
    else $error("Async reset did not clear state immediately");

  // While rst is low, state is held cleared
  assert property (@(posedge clk) (!rst |-> (ac97_rst_==1'b0 && cnt==3'd0 && ps_cnt==6'd0)))
    else $error("State not held cleared while rst low");

  // All other properties use synchronous sampling and ignore while rst low
  default disable iff (!rst);

  // ps_ce definition and pulse behavior
  assert property (ps_ce == (ps_cnt == PS_TICKS))
    else $error("ps_ce != (ps_cnt == PS_TICKS)");

  assert property ($rose(ps_ce) |-> ##1 !ps_ce)
    else $error("ps_ce not single-cycle");

  assert property (ps_ce || rst_force |=> ps_cnt==6'd0)
    else $error("ps_cnt not cleared after ps_ce or rst_force");

  assert property ((!ps_ce && !rst_force) |-> ps_cnt == $past(ps_cnt)+6'd1)
    else $error("ps_cnt did not increment when expected");

  // ce definition
  assert property (ce == (ps_ce && (cnt != RST_DEL)))
    else $error("ce != ps_ce && (cnt != RST_DEL)");

  // cnt behavior: increments only on ce, holds otherwise, and saturates at RST_DEL
  assert property (ce |=> cnt == $past(cnt)+3'd1)
    else $error("cnt did not increment on ce");

  assert property ((!ce && !rst_force) |-> $stable(cnt))
    else $error("cnt changed without ce/rst_force");

  assert property ((cnt == RST_DEL) |-> $stable(cnt))
    else $error("cnt changed after reaching RST_DEL");

  // to definition
  assert property (to == (cnt == RST_DEL))
    else $error("to != (cnt == RST_DEL)");

  // ac97_rst_ deasserts exactly when to goes high and then sticks until reset/rst_force
  assert property ($rose(to) |-> ($past(ac97_rst_)==1'b0 && ac97_rst_==1'b1))
    else $error("ac97_rst_ did not rise with to");

  assert property ($rose(ac97_rst_) |-> to)
    else $error("ac97_rst_ rose without to");

  assert property ($fell(ac97_rst_) |-> (!rst || $past(rst_force)))
    else $error("ac97_rst_ fell without rst low or rst_force");

  assert property (ac97_rst_ && !rst_force |=> ac97_rst_)
    else $error("ac97_rst_ not sticky high");

  // ps_ce periodicity (allows interruption by rst_force)
  assert property ($rose(ps_ce) |-> (!ps_ce[*PS_TICKS] ##1 (ps_ce || rst_force)))
    else $error("ps_ce period not equal to PS_TICKS+1");

  // Coverage
  cover property ($rose(ps_ce));
  cover property (ce);
  cover property ($rose(to));
  cover property ($rose(ac97_rst_));
  cover property (rst && !rst_force && !ac97_rst_ ##1 ce[*RST_DEL] ##1 to && ac97_rst_);
endmodule

// Bind into the DUT
bind ac97_rst ac97_rst_sva i_ac97_rst_sva (
  .clk       (clk),
  .rst       (rst),
  .rst_force (rst_force),
  .ps_ce     (ps_ce),
  .ac97_rst_ (ac97_rst_),
  .cnt       (cnt),
  .ce        (ce),
  .to        (to),
  .ps_cnt    (ps_cnt)
);

`endif