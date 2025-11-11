// SVA for binary_counter
module binary_counter_sva(
  input logic       clk,
  input logic       rst,
  input logic [3:0] count
);

  default clocking cb @(posedge clk); endclocking

  // Track that $past() is valid
  bit past_valid;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // 1) Synchronous reset: when rst is 1 at a clock, count must be 0 that same clock
  assert property (rst |-> count == 4'h0);

  // 2) After deasserting reset (previous cycle rst=1, now rst=0), count must be 1
  assert property (past_valid && $past(rst) && !rst |-> count == 4'h1);

  // 3) Normal increment when rst stays low across adjacent cycles and prior count is known
  assert property (past_valid && !rst && !$past(rst) && !$isunknown($past(count))
                   |-> count == $past(count) + 4'h1);

  // 4) Explicit wrap check on 0xF -> 0x0 when not in reset across adjacent cycles
  assert property (past_valid && !rst && !$past(rst) && ($past(count) == 4'hF)
                   |-> count == 4'h0);

  // Coverage

  // See reset asserted and then deasserted
  cover property (rst);
  cover property ($fell(rst));

  // See at least one valid increment (rst low across cycles)
  cover property (past_valid && !rst && !$past(rst) && !$isunknown($past(count))
                  && (count == $past(count) + 4'h1));

  // See explicit wrap E->F->0 with rst low
  cover property (past_valid && !rst && !$past(rst) && ($past(count) == 4'hE)
                  ##1 (count == 4'hF && !rst) ##1 (count == 4'h0 && !rst));

  // See a full post-reset run 1..F->0
  cover property ($fell(rst)
                  ##1 (count==4'h1 && !rst)
                  ##1 (count==4'h2 && !rst)
                  ##1 (count==4'h3 && !rst)
                  ##1 (count==4'h4 && !rst)
                  ##1 (count==4'h5 && !rst)
                  ##1 (count==4'h6 && !rst)
                  ##1 (count==4'h7 && !rst)
                  ##1 (count==4'h8 && !rst)
                  ##1 (count==4'h9 && !rst)
                  ##1 (count==4'hA && !rst)
                  ##1 (count==4'hB && !rst)
                  ##1 (count==4'hC && !rst)
                  ##1 (count==4'hD && !rst)
                  ##1 (count==4'hE && !rst)
                  ##1 (count==4'hF && !rst)
                  ##1 (count==4'h0 && !rst));

endmodule

// Bind into the DUT
bind binary_counter binary_counter_sva sva_i(.clk(clk), .rst(rst), .count(count));