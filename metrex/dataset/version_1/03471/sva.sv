// SVA for clk_generator
// Bind this file alongside the DUT

module clk_generator_sva(
  input              clk,
  input              rst,
  input              en,
  input       [31:0] limit,
  input       [31:0] count,
  input              clk_0,
  input              done,
  input       [31:0] ndCount,
  input       [31:0] initCount
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst)

  // Safety: no X after reset deasserted
  assert property ( !$isunknown({clk_0, done, ndCount, initCount}) );

  // initCount should be constant after time 0 (RTL never reassigns it)
  assert property ( $stable(initCount) );

  // Asynchronous reset: immediate effect
  assert property (@(negedge rst) (clk_0==1'b0 && ndCount==32'h0 && done==1'b0));

  // While in reset, hold reset values
  assert property (@(posedge clk) !rst |-> (clk_0==1'b0 && ndCount==32'h0 && done==1'b0));

  // When en=0 (previous cycle), load initCount and clear outputs
  assert property ( $past(!en) |-> (ndCount==initCount && clk_0==1'b0 && done==1'b0) );

  // Counting step when en=1 and ndCount < limit (previous cycle)
  assert property ( $past(en && ($past(ndCount) < $past(limit)))
                    |-> (ndCount == $past(ndCount)+1 && done==1'b0 && clk_0==$past(clk_0)) );

  // Wrap/reset when en=1 and ndCount >= limit (previous cycle)
  assert property ( $past(en && ($past(ndCount) >= $past(limit)))
                    |-> (ndCount==initCount && done==1'b1 && clk_0==1'b0) );

  // done must only assert on a wrap
  assert property ( done |-> $past(en && ($past(ndCount) >= $past(limit))) );

  // If initCount < limit, done is a single-cycle pulse
  assert property ( ($rose(done) && (initCount < $past(limit))) |-> ##1 !done );

  // Per current RTL, clk_0 can never be 1 (highlights unreachable toggle)
  assert property ( clk_0==1'b0 );

  // Coverage

  // See at least one count-up followed by a done pulse
  cover property ( (initCount < limit) && en && (ndCount < limit)
                   ##1 en && (ndCount == $past(ndCount)+1)
                   ##[1:$] done );

  // Limit==0 corner: done stays high with en
  cover property ( en && (limit==0) ##1 done ##1 done );

  // en drop reloads initCount and clears outputs
  cover property ( $fell(en) ##1 (ndCount==initCount && done==1'b0 && clk_0==1'b0) );

  // Try to see clk_0 ever go high (should be unreachable with this RTL)
  cover property ( clk_0==1'b1 );

endmodule

bind clk_generator clk_generator_sva sva_i(
  .clk(clk),
  .rst(rst),
  .en(en),
  .limit(limit),
  .count(count),
  .clk_0(clk_0),
  .done(done),
  .ndCount(ndCount),
  .initCount(initCount)
);