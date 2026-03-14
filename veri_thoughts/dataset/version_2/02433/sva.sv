module traffic_light_controller_sva (
  input logic clk,
  input logic green,
  input logic yellow,
  input logic red
);
  // Clock: clk (posedge). Reset: none. Logic: sequential always @(posedge clk). Outputs: green/yellow/red exclusive per branch.

  // Green high implies Yellow and Red low.
  check_green_exclusive: assert property (
    @(posedge clk) green |-> (!yellow && !red)
  );

  // Yellow high implies Green and Red low.
  check_yellow_exclusive: assert property (
    @(posedge clk) yellow |-> (!green && !red)
  );

  // Red high implies Green and Yellow low.
  check_red_exclusive: assert property (
    @(posedge clk) red |-> (!green && !yellow)
  );

  // No simultaneous rises with Green.
  check_no_multi_rise_green: assert property (
    @(posedge clk) $rose(green) |-> (!$rose(yellow) && !$rose(red))
  );

  // No simultaneous rises with Yellow.
  check_no_multi_rise_yellow: assert property (
    @(posedge clk) $rose(yellow) |-> (!$rose(green) && !$rose(red))
  );

  // No simultaneous rises with Red.
  check_no_multi_rise_red: assert property (
    @(posedge clk) $rose(red) |-> (!$rose(green) && !$rose(yellow))
  );

  // If Green falls, another color is ON that cycle.
  check_green_fall_implies_other_on: assert property (
    @(posedge clk) $fell(green) |-> (yellow || red)
  );

  // If Yellow falls, another color is ON that cycle.
  check_yellow_fall_implies_other_on: assert property (
    @(posedge clk) $fell(yellow) |-> (green || red)
  );

  // If Red falls, another color is ON that cycle.
  check_red_fall_implies_other_on: assert property (
    @(posedge clk) $fell(red) |-> (green || yellow)
  );

  // Any output change results in a one-hot state.
  check_change_results_onehot: assert property (
    @(posedge clk) ($changed(green) || $changed(yellow) || $changed(red))
      |-> ((green && !yellow && !red) || (!green && yellow && !red) || (!green && !yellow && red))
  );

endmodule