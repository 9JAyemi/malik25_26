// SVA for clock_divider
module clock_divider_sva #(parameter int unsigned DIV = 32'd50_000_000) (
  input logic        clk_50,
  input logic        clk_1,
  input logic [31:0] counter,
  input logic        VPWR, VPB, VGND, VNB
);

  default clocking cb @(posedge clk_50); endclocking

  // Enable $past after first sampled edge
  logic started;
  always_ff @(posedge clk_50) started <= 1'b1;

  // Helpers
  let known_clk1 = !($isunknown(clk_1) || $isunknown($past(clk_1)));
  let toggled    = known_clk1 && (clk_1 != $past(clk_1));

  // Supplies are correct constants
  assert property (@(posedge clk_50) (VPWR===1'b1) && (VPB===1'b1) && (VGND===1'b0) && (VNB===1'b0))
    else $error("Supply rails incorrect");

  // Counter never exceeds DIV
  assert property (disable iff (!started) counter <= DIV)
    else $error("Counter exceeded DIV");

  // Counter increments by 1 when not wrapping
  assert property (disable iff (!started) ($past(counter) != DIV) |-> (counter == $past(counter)+1))
    else $error("Counter did not increment by 1");

  // Counter wraps to 0 when reaching DIV
  assert property (disable iff (!started) ($past(counter) == DIV) |-> (counter == 32'd0))
    else $error("Counter did not wrap to 0 at DIV");

  // clk_1 toggles iff counter wraps
  assert property (disable iff (!started) (($past(counter) == DIV) && known_clk1) |-> (clk_1 == ~$past(clk_1)))
    else $error("clk_1 failed to toggle on wrap");

  assert property (disable iff (!started) (($past(counter) != DIV) && known_clk1) |-> (clk_1 == $past(clk_1)))
    else $error("Spurious clk_1 toggle without wrap");

  assert property (disable iff (!started) toggled |-> ($past(counter) == DIV))
    else $error("clk_1 toggled without counter at DIV");

  // Exact toggle periodicity: every DIV+1 input clock cycles
  assert property (disable iff (!started) toggled |-> (!toggled[*DIV] ##1 toggled))
    else $error("clk_1 toggle period not equal to DIV+1");

  // Coverage
  cover property (disable iff (!started) counter == DIV);
  cover property (disable iff (!started) ($past(counter) == DIV && counter == 0));
  cover property (disable iff (!started) toggled);
  cover property (disable iff (!started) (toggled ##1 !toggled[*DIV] ##1 toggled));

endmodule

bind clock_divider clock_divider_sva #(.DIV(32'd50_000_000)) i_clock_divider_sva (
  .clk_50(clk_50),
  .clk_1(clk_1),
  .counter(counter),
  .VPWR(VPWR),
  .VPB(VPB),
  .VGND(VGND),
  .VNB(VNB)
);