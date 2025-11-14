// SVA for zet_rxr16: rotate-right (e=0) and rotate-right-through-carry (e=1)
module zet_rxr16_sva
(
  input  logic        clk,
  input  logic        rst_n,      // tie high if unused
  input  logic [15:0] x,
  input  logic        ci,
  input  logic [ 4:0] y,
  input  logic        e,
  input  logic [15:0] w,
  input  logic        co
);

  // helpers
  function automatic [15:0] rotr16(input [15:0] xv, input int unsigned sh);
    if (sh==0 || sh>16) rotr16 = xv;
    else                rotr16 = {xv[sh-1:0], xv[15:sh]};
  endfunction
  function automatic [16:0] rorc16(input [15:0] xv, input logic civ, input int unsigned sh);
    if (sh==0 || sh>16) rorc16 = {civ, xv};
    else                rorc16 = {xv[sh-1:0], civ, xv[15:sh]};
  endfunction

  // no X/Z on outputs when inputs are known
  assert property (@(posedge clk) disable iff (!rst_n)
                   !$isunknown({y,e,ci,x}) |-> ##0 !$isunknown({co,w}))
    else $error("zet_rxr16: X/Z on outputs with known inputs");

  // default case: y==0 or y>16 -> pass-through
  assert property (@(posedge clk) disable iff (!rst_n)
                   ((y==5'd0) || (y>5'd16)) |-> ##0 {co,w} == {ci,x})
    else $error("zet_rxr16: default pass-through mismatch");

  // e==0: pure rotate-right for y in [1:15]
  assert property (@(posedge clk) disable iff (!rst_n)
                   (e==1'b0 && (y inside {[5'd1:5'd15]})) |-> ##0 {co,w} == {ci, rotr16(x, int'(y))})
    else $error("zet_rxr16: e=0 rotate-right mismatch");

  // y==16 (both e values): matches case entry {x,ci}
  assert property (@(posedge clk) disable iff (!rst_n)
                   (y==5'd16) |-> ##0 {co,w} == {x,ci})
    else $error("zet_rxr16: y=16 behavior mismatch");

  // e==1: rotate-right-through-carry for y in [1:16]
  assert property (@(posedge clk) disable iff (!rst_n)
                   (e==1'b1 && (y inside {[5'd1:5'd16]})) |-> ##0 {co,w} == rorc16(x, ci, int'(y)))
    else $error("zet_rxr16: e=1 RORC mismatch");

  // simple functional covers (hit key modes/edges)
  cover property (@(posedge clk) disable iff (!rst_n) (y==5'd0) && (e==0));
  cover property (@(posedge clk) disable iff (!rst_n) (y==5'd1) && (e==0));
  cover property (@(posedge clk) disable iff (!rst_n) (y inside {[5'd2:5'd15]}) && (e==0));
  cover property (@(posedge clk) disable iff (!rst_n) (y==5'd16) && (e==0));
  cover property (@(posedge clk) disable iff (!rst_n) (y>5'd16) && (e==0));

  cover property (@(posedge clk) disable iff (!rst_n) (y==5'd1)  && (e==1));
  cover property (@(posedge clk) disable iff (!rst_n) (y==5'd16) && (e==1));
  cover property (@(posedge clk) disable iff (!rst_n) (y inside {[5'd2:5'd15]}) && (e==1));

  // edge-pattern covers for carry behavior
  cover property (@(posedge clk) disable iff (!rst_n) (e==1) && (y inside {[5'd1:5'd16]}) && (x==16'h0001) ##0 (co==((y==0)?ci:x[int'(y)-1])));
  cover property (@(posedge clk) disable iff (!rst_n) (e==1) && (y inside {[5'd1:5'd16]}) && (x==16'h8000) ##0 (co==((y==0)?ci:x[int'(y)-1])));

  // toggle coverage on e
  cover property (@(posedge clk) disable iff (!rst_n) $rose(e));
  cover property (@(posedge clk) disable iff (!rst_n) $fell(e));

endmodule

// Example bind (provide clk/rst_n from your TB):
// bind zet_rxr16 zet_rxr16_sva sva(.clk(tb_clk), .rst_n(tb_rst_n), .x(x), .ci(ci), .y(y), .e(e), .w(w), .co(co));