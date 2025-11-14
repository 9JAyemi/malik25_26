// SVA for frame_detector
// Bind into DUT to check functionality and add concise coverage.

module frame_detector_sva
(
  input  logic        clk400,
  input  logic        clk80,
  input  logic        reset,
  input  logic        enable,
  input  logic        sdata,

  input  logic [5:0]  s,
  input  logic        detect,
  input  logic [2:0]  c,
  input  logic [4:0]  p,
  input  logic        e,

  input  logic [4:0]  pdata,
  input  logic        error
);

  // 400 MHz domain: reset values
  assert property (@(posedge clk400) reset |-> (s==6'd0 && detect==1'b0 && c==3'd0 && p==5'd0 && e==1'b0));

  // 400 MHz domain: hold when !enable
  assert property (@(posedge clk400) disable iff (reset)
                   !enable |=> (s==$past(s) && detect==$past(detect) && c==$past(c) && p==$past(p) && e==$past(e)));

  // 400 MHz domain: shift register behavior
  assert property (@(posedge clk400) disable iff (reset)
                   enable |=> s == {$past(s[4:0]), $past(sdata)});

  // 400 MHz domain: detect equals function of prior s when prior enable=1
  assert property (@(posedge clk400) disable iff (reset)
                   $past(enable) |-> detect == ( ($past(s)==6'b100000) || ($past(s)==6'b011111) ));

  // 400 MHz domain: counter c update (resets on prior sync or prior detect)
  assert property (@(posedge clk400) disable iff (reset)
                   $past(enable) |-> c == ( ($past(c[2]) || $past(detect)) ? 3'd0 : ($past(c)+3'd1) ));

  // 400 MHz domain: c never exceeds 4, and c[2] implies c==4
  assert property (@(posedge clk400) disable iff (reset) c <= 3'd4);
  assert property (@(posedge clk400) disable iff (reset) c[2] |-> c==3'd4);

  // 400 MHz domain: p capture on prior sync, else hold
  assert property (@(posedge clk400) disable iff (reset)
                   $past(enable) |-> p == ( $past(c[2]) ? $past(s[5:1]) : $past(p) ));

  // 400 MHz domain: e semantics (clear on prior sync, set on prior detect, else hold)
  assert property (@(posedge clk400) disable iff (reset)
                   $past(enable) |-> e == ( $past(c[2]) ? 1'b0 : ( $past(detect) ? 1'b1 : $past(e) ) ));

  // 80 MHz domain: reset values
  assert property (@(posedge clk80) reset |-> (pdata==5'd0 && error==1'b0));

  // 80 MHz domain: when enable=1, outputs reflect p/e; when enable=0, outputs forced to 0
  assert property (@(posedge clk80) disable iff (reset) enable  |-> (pdata==p && error==e));
  assert property (@(posedge clk80) disable iff (reset) !enable |-> (pdata==5'd0 && error==1'b0));

  // ---------------- Coverage ----------------

  // Cover both detect patterns being recognized
  cover property (@(posedge clk400) disable iff (reset) (enable && s==6'b100000) ##1 detect);
  cover property (@(posedge clk400) disable iff (reset) (enable && s==6'b011111) ##1 detect);

  // Cover counter sequence 0->1->2->3->4->0 under enable
  cover property (@(posedge clk400) disable iff (reset)
                  (enable && c==3'd0) ##1 (enable && c==3'd1) ##1 (enable && c==3'd2)
                  ##1 (enable && c==3'd3) ##1 (enable && c==3'd4) ##1 (enable && c==3'd0));

  // Cover e being set by detect then cleared by a sync
  cover property (@(posedge clk400) disable iff (reset)
                  detect ##1 (e==1) ##[1:20] (c[2]) ##1 (e==0));

  // Cover p capturing s[5:1] on a sync
  cover property (@(posedge clk400) disable iff (reset) c[2] ##1 (p==$past(s[5:1])));

  // Cover clk80 sampling in both modes
  cover property (@(posedge clk80)  disable iff (reset) enable  && (pdata==p) && (error==e));
  cover property (@(posedge clk80)  disable iff (reset) !enable && (pdata==5'd0) && (error==1'b0));

endmodule

bind frame_detector frame_detector_sva sva_i (
  .clk400(clk400),
  .clk80(clk80),
  .reset(reset),
  .enable(enable),
  .sdata(sdata),
  .s(s),
  .detect(detect),
  .c(c),
  .p(p),
  .e(e),
  .pdata(pdata),
  .error(error)
);