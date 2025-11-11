// SVA for dffs_6: 6-bit DFF with async set (active-high)
module dffs_6_sva #(parameter W=6) (
  input logic              clk,
  input logic              set,
  input logic [W-1:0]      d,
  input logic [W-1:0]      q
);
  localparam logic [W-1:0] ALL1 = {W{1'b1}};

  // 1) Asynchronous set takes immediate effect
  property p_async_set_immediate;
    @(posedge set) 1 |-> ##0 (q == ALL1);
  endproperty
  assert property (p_async_set_immediate);

  // 2) While set is asserted, q must be all 1s (set has priority over clk)
  property p_set_level_holds_ones;
    @(posedge clk or posedge set) set |-> ##0 (q == ALL1);
  endproperty
  assert property (p_set_level_holds_ones);

  // 3) Synchronous load on clk when set is not taking effect
  property p_sync_load_d;
    @(posedge clk) (!set && !$rose(set)) |-> ##0 (q == $sampled(d));
  endproperty
  assert property (p_sync_load_d);

  // 4) After set deasserts, q stays 1s until the next clk edge updates it
  property p_hold_ones_until_clk;
    @(negedge set) 1 |-> (q == ALL1) until_with $rose(clk);
  endproperty
  assert property (p_hold_ones_until_clk);

  // 5) X-checks at update points
  assert property (@(posedge clk or posedge set) !$isunknown(q));
  assert property (@(posedge clk) (!set && !$rose(set)) |-> !$isunknown($sampled(d)));

  // Coverage

  // C1: Observe async set and its effect
  cover property (@(posedge set) ##0 (q == ALL1));

  // C2: Coincident clk & set (set priority)
  cover property (@(posedge clk) $rose(set) ##0 (q == ALL1));

  // C3: Synchronous load of 0 and ALL1 values
  cover property (@(posedge clk) (!set && !$rose(set) && (d == '0))  ##0 (q == '0));
  cover property (@(posedge clk) (!set && !$rose(set) && (d == ALL1)) ##0 (q == ALL1));

  // C4: Two back-to-back synchronous loads with set low
  cover property (@(posedge clk) (!set && !$rose(set)) ##1 (!set && !$rose(set)));
endmodule

// Bind into DUT
bind dffs_6 dffs_6_sva #(.W(6)) dffs_6_sva_i (.clk(clk), .set(set), .d(d), .q(q));