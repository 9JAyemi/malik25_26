// SVA for clk_generator
module clk_generator_sva (
  input logic         clk,
  input logic         en,
  input logic [31:0]  limit,
  input logic [31:0]  count,
  input logic         clk_0,
  input logic [31:0]  ndCount
);

  // Default sampling on the DUT's active edge
  default clocking cb @(negedge clk); endclocking

  // Initialization checks (simulation-time)
  initial begin
    assert (clk_0 == 1'b0) else $error("clk_0 not initialized to 0");
    assert (ndCount == 32'h0) else $error("ndCount not initialized to 0");
  end

  // Sanity: no X/Z on key controls/operands at sampling
  a_no_x_inputs: assert property (!$isunknown({en, count, limit}));

  // No unintended updates on posedge clk (DUT updates only at negedge)
  a_no_posedge_updates_clk0: assert property (@(posedge clk) $stable(clk_0));
  a_no_posedge_updates_nd:   assert property (@(posedge clk) $stable(ndCount));

  // Partition well-defined when enabled (detect X in compare)
  a_compare_well_defined: assert property (en |-> ((count > ndCount) ^ (count <= ndCount)));

  // Disabled behavior: force low and preload next deadline
  a_disable_behavior: assert property ((!en) |-> ##0 (clk_0 == 1'b0 && ndCount == count + limit));

  // Hold branch: when enabled and not past deadline, outputs hold
  a_hold_when_not_due: assert property (en && (count <= ndCount) |-> ##0 ($stable(clk_0) && $stable(ndCount)));

  // Toggle branch: when enabled and count surpasses deadline, toggle and advance deadline
  a_toggle_when_due: assert property (en && (count > ndCount) |-> ##0 (clk_0 == !$past(clk_0) && ndCount == count + limit));

  // ndCount may only change on disable or due-tick
  a_ndcount_change_legal: assert property (##0 $changed(ndCount) |-> (!en) || (en && (count > ndCount)));

  // clk_0 may only change on disable (to 0) or due-tick (toggle)
  a_clk0_change_legal: assert property (##0 $changed(clk_0) |-> ((!en && clk_0 == 1'b0) || (en && (count > ndCount))));

  // Coverage: exercise each branch and multiple toggles while enabled
  c_disable_branch:  cover property (!en ##1 !en);
  c_hold_branch:     cover property (en && (count <= ndCount));
  c_toggle_branch:   cover property (en && (count > ndCount) ##0 (clk_0 == !$past(clk_0)));
  c_two_toggles_en:  cover property ((en && (count > ndCount) ##0 (clk_0 == !$past(clk_0)))
                                     ##[1:$] (en && (count > ndCount) ##0 (clk_0 == !$past(clk_0))));
endmodule

// Bind to all instances of clk_generator
bind clk_generator clk_generator_sva sva_i (
  .clk    (clk),
  .en     (en),
  .limit  (limit),
  .count  (count),
  .clk_0  (clk_0),
  .ndCount(ndCount)
);