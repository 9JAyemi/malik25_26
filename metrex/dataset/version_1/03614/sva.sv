// SVA for reset_resync. Focused, concise, and high-quality checks.
// Bind-friendly and parameterized.

`ifndef RESET_RESYNC_SVA
`define RESET_RESYNC_SVA

module reset_resync_sva #(
  parameter VALUE_DURING_RESET = 1
) (
  input  logic rst_in,
  input  logic clk_in,
  input  logic clk_out,
  input  logic rst_out,
  input  logic rst_in_dly
);

  // Power-up value
  initial assert (rst_out === VALUE_DURING_RESET)
    else $error("rst_out initial value != VALUE_DURING_RESET");

  // rst_in_dly semantics
  assert property (@(posedge rst_in) ##0 rst_in_dly)
    else $error("rst_in_dly must assert immediately on rst_in rise");

  assert property (@(posedge clk_in) !rst_in |-> ##0 !rst_in_dly)
    else $error("rst_in_dly must clear on clk_in edge when rst_in is low");

  // While rst_in is high, rst_in_dly must remain high (post-update sampling)
  assert property (@(posedge clk_in or posedge rst_in) ##0 (rst_in -> rst_in_dly))
    else $error("rst_in_dly must follow rst_in high");

  // rst_out semantics: async assert, sync deassert
  assert property (@(posedge rst_in_dly) ##0 (rst_out == VALUE_DURING_RESET))
    else $error("rst_out must go to VALUE_DURING_RESET on rst_in_dly rise");

  // While rst_in_dly is high, rst_out must be VALUE_DURING_RESET (post-update sampling)
  assert property (@(posedge clk_out or posedge rst_in_dly) ##0 (rst_in_dly -> (rst_out == VALUE_DURING_RESET)))
    else $error("rst_out must hold reset value while rst_in_dly is high");

  // On clk_out when rst_in_dly is low, rst_out must be released value
  assert property (@(posedge clk_out) !rst_in_dly |-> ##0 (rst_out == ~VALUE_DURING_RESET))
    else $error("rst_out must be ~VALUE_DURING_RESET on clk_out when rst_in_dly is low");

  // After rst_in_dly falls, rst_out must stay in reset until the next clk_out edge
  assert property (@(negedge rst_in_dly) (rst_out == VALUE_DURING_RESET) until_with (@(posedge clk_out) 1'b1))
    else $error("rst_out deassert must be synchronous to clk_out");

  // rst_out can only change on posedge rst_in_dly or posedge clk_out
  assert property (@(posedge clk_out or posedge rst_in_dly) $changed(rst_out) |-> ($rose(rst_in_dly) || $rose(clk_out)))
    else $error("rst_out changed without an allowed event");

  // No X/Z on rst_out at architectural update events
  assert property (@(posedge clk_out or posedge rst_in_dly) ##0 !$isunknown(rst_out))
    else $error("rst_out is X/Z");

  // Coverage: basic scenarios
  cover property (@(posedge rst_in) ##0 (rst_out == VALUE_DURING_RESET));
  cover property (@(negedge rst_in)
                  ##[1:$] @(posedge clk_in) (!rst_in_dly)
                  ##[1:$] @(posedge clk_out) (rst_out == ~VALUE_DURING_RESET));
  cover property (@(posedge rst_in)
                  ##[1:$] @(negedge rst_in)
                  ##[1:$] @(posedge clk_in)
                  ##[1:$] @(posedge clk_out));

endmodule

// Bind into the DUT (accesses internal rst_in_dly)
bind reset_resync reset_resync_sva #(.VALUE_DURING_RESET(VALUE_DURING_RESET)) u_reset_resync_sva (
  .rst_in(rst_in),
  .clk_in(clk_in),
  .clk_out(clk_out),
  .rst_out(rst_out),
  .rst_in_dly(rst_in_dly)
);

`endif