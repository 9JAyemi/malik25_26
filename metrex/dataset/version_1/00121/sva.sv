// SVA for binary_counter
module binary_counter_sva #(parameter WIDTH=4) (
  input logic              clk,
  input logic              rst,
  input logic              en,
  input logic              load,
  input logic [WIDTH-1:0]  q,
  input logic [WIDTH-1:0]  q_bar
);

  default clocking cb @(posedge clk); endclocking

  logic past_valid;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // Combinational complement check (post-NBA)
  assert property (1'b1 |-> ##0 (q_bar == ~q))
    else $error("q_bar must be complement of q");

  // Outputs known (after first sampled cycle)
  assert property (past_valid |-> (!$isunknown(q) && !$isunknown(q_bar)));

  // Synchronous reset
  assert property (rst |=> (q == '0));

  // Next-state behavior (priority: rst > en > load > hold)
  assert property (past_valid && !rst && en            |=> (q == $past(q) + 1));
  assert property (past_valid && !rst && !en && load   |=> (q == ~$past(q)));
  assert property (past_valid && !rst && !en && !load  |=> (q == $past(q)));
  // Explicit en over load when both asserted
  assert property (past_valid && !rst && en && load    |=> (q == $past(q) + 1));

  // Wrap-around on increment
  assert property (past_valid && !rst && en && ($past(q) == {WIDTH{1'b1}}) |=> (q == '0));

  // Coverage
  cover property (rst);
  cover property (past_valid && !rst && en            |=> (q == $past(q) + 1));
  cover property (past_valid && !rst && !en && load   |=> (q == ~$past(q)));
  cover property (past_valid && !rst && !en && !load  |=> (q == $past(q)));
  cover property (past_valid && !rst && en && load    |=> (q == $past(q) + 1));
  cover property (past_valid && !rst && en && ($past(q) == {WIDTH{1'b1}}) |=> (q == '0));

endmodule

// Bind into DUT
bind binary_counter binary_counter_sva #(.WIDTH(4)) u_binary_counter_sva (
  .clk  (clk),
  .rst  (rst),
  .en   (en),
  .load (load),
  .q    (q),
  .q_bar(q_bar)
);