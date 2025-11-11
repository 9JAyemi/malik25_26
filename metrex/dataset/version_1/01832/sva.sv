// SVA for inc_module: concise, high-quality checks and coverage
// Bind into DUT to access internal SW_reg
module inc_module_sva (
  input logic        clk,
  input logic        reset,
  input logic [2:0]  SW,
  input logic [3:0]  LED,
  input logic [2:0]  SW_reg
);
  default clocking cb @(posedge clk); endclocking

  // Reset behavior: while in reset, outputs/regs are 0
  assert property (@cb reset |-> (LED == 4'd0 && SW_reg == 3'd0));

  // First cycle after reset releases (prev was in reset)
  assert property (@cb $past(reset) && !reset |-> (LED == 4'd1 && SW_reg == SW));

  // Pipeline flop: SW_reg captures SW (skip during/just-after reset)
  assert property (@cb disable iff (reset || $past(reset)) SW_reg == $past(SW));

  // LED is SW_reg + 1 from prior cycle (skip during/just-after reset)
  assert property (@cb disable iff (reset || $past(reset)) LED == $past(SW_reg) + 1);

  // End-to-end: LED equals prior-cycle SW + 1 (functional intent)
  assert property (@cb disable iff (reset || $past(reset)) LED == $past(SW) + 1);

  // No X/Z when not in reset
  assert property (@cb !reset |-> (!$isunknown(LED) && !$isunknown(SW_reg)));

  // Coverage: exercise mapping for all SW values
  genvar i;
  generate for (i=0; i<8; i++) begin : C_MAP
    cover property (@cb disable iff (reset || $past(reset))
                    ($past(SW) == i) && (LED == (i+1)));
  end endgenerate

  // Coverage: reset pulse and return to function
  cover property (@cb $rose(reset) ##1 reset ##1 !reset ##1 (LED == 4'd1));
endmodule

// Bind into the DUT
bind inc_module inc_module_sva SVA (
  .clk   (clk),
  .reset (reset),
  .SW    (SW),
  .LED   (LED),
  .SW_reg(SW_reg)
);