// SVA for BOR. Bind this file to the DUT.
// Focus: correctness of reset behavior, counter updates, and timing.

module BOR_sva #(parameter int T_RESET = 10)
(
  input logic        clk,
  input logic        vcc,
  input logic        vth,
  input logic        rst,
  input logic [7:0]  counter
);

  default clocking cb @(posedge clk); endclocking

  logic past_valid;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // Basic sanity: no X/Z on key signals after first cycle
  assert property (past_valid |-> !$isunknown({vcc, vth, rst, counter}));

  // Brown-out must assert reset that cycle
  assert property ((vcc < vth) |-> rst);

  // Deassert path: when vcc good and prior counter met threshold, drop rst and clear counter
  assert property (past_valid && (vcc >= vth && $past(counter) >= T_RESET) |-> (!rst && counter == 8'd0));

  // Non-deassert path: counter increments every cycle
  assert property (past_valid && !(vcc >= vth && $past(counter) >= T_RESET) |-> counter == $past(counter) + 8'd1);

  // While counting after good vcc (pre-release), rst holds its previous value
  assert property (past_valid && (vcc >= vth && $past(counter) < T_RESET) |-> rst == $past(rst));

  // Edge checks
  assert property (past_valid && $rose(rst) |-> (vcc < vth));
  assert property (past_valid && $fell(rst) |-> (vcc >= vth && $past(counter) >= T_RESET && counter == 8'd0));
  assert property (past_valid && $fell(rst) ##1 (counter == 8'd1));

  // Progress: sustained good vcc guarantees reset deassert no later than T_RESET cycles later
  assert property (disable iff (!past_valid) ( (vcc >= vth)[*T_RESET] ##1 !rst ));

  // Safety: never deassert while vcc is below threshold
  assert property ((vcc < vth) |-> rst);

  // Coverage: key scenarios
  // 1) Brown-out, recovery, and timed release
  cover property ( (vcc < vth)[*1:$] ##1 (vcc >= vth)[*T_RESET] ##1 !rst );

  // 2) Long brown-out causing immediate release on first good cycle
  cover property ( (vcc < vth)[*(T_RESET+2)] ##1 (vcc >= vth && !rst) );

  // 3) Counter free-running increment (including wrap) on non-deassert cycles
  cover property (past_valid && !(vcc >= vth && $past(counter) >= T_RESET) && $past(counter) == 8'hFF ##1 counter == 8'h00);

endmodule

// Bind into DUT
bind BOR BOR_sva #(.T_RESET(t_reset)) BOR_sva_i (
  .clk(clk),
  .vcc(vcc),
  .vth(vth),
  .rst(rst),
  .counter(counter)
);