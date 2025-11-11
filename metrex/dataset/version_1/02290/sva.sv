// SVA for mux4x1
module mux4x1_sva #(parameter W=144)(
  input clk,
  input rst,
  input sel0,
  input sel1,
  input  [W-1:0] port0_ci,
  input  [W-1:0] port1_ci,
  input  [W-1:0] port2_ci,
  input  [W-1:0] port3_ci,
  input  [W-1:0] port_co
);

  function automatic [W-1:0] f_mux(input logic [1:0] s,
                                   input [W-1:0] a,b,c,d);
    case (s)
      2'b00: f_mux = a;
      2'b01: f_mux = b;
      2'b10: f_mux = c;
      2'b11: f_mux = d;
      default: f_mux = 'x;
    endcase
  endfunction

  // Reset behavior
  assert property (@(posedge clk) rst |-> port_co == '0);
  assert property (@(posedge rst) 1 |-> ##0 port_co == '0);

  // Functional correctness (one-cycle lookback to align with flop semantics)
  assert property (@(posedge clk)
    !rst && !$past(rst) && !$isunknown($past({sel1,sel0})) |->
    $past(port_co) == f_mux($past({sel1,sel0}),
                            $past(port0_ci), $past(port1_ci),
                            $past(port2_ci), $past(port3_ci)));

  // Knownness when inputs/select are known
  assert property (@(posedge clk)
    !rst && !$past(rst) &&
    !$isunknown($past({sel1,sel0})) &&
    !$isunknown(f_mux($past({sel1,sel0}),
                      $past(port0_ci), $past(port1_ci),
                      $past(port2_ci), $past(port3_ci))) |->
    !$isunknown($past(port_co)));

  // Coverage: each select value exercised
  cover property (@(posedge clk) !rst && {sel1,sel0}==2'b00);
  cover property (@(posedge clk) !rst && {sel1,sel0}==2'b01);
  cover property (@(posedge clk) !rst && {sel1,sel0}==2'b10);
  cover property (@(posedge clk) !rst && {sel1,sel0}==2'b11);

  // Coverage: selected input observed on output next cycle
  cover property (@(posedge clk)
    !rst && !$isunknown({sel1,sel0}) ##1
    port_co == f_mux($past({sel1,sel0}),
                     $past(port0_ci), $past(port1_ci),
                     $past(port2_ci), $past(port3_ci)));

  // Coverage: reset event
  cover property (@(posedge rst) 1);

endmodule

bind mux4x1 mux4x1_sva #(.W(144)) u_mux4x1_sva (.*);