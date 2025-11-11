// SVA for clk_1_khz: checks modulo-8 counter and exact/only-on-wrap toggle, with concise coverage.
module clk_1_khz_sva (
  input  logic        clk_50mhz,
  input  logic        clk_1khz,
  input  logic [3:0]  count
);
  default clocking cb @(posedge clk_50mhz); endclocking
  default disable iff ($initstate || $isunknown({clk_1khz,count}));

  // Count progression and wrap (mod-8)
  assert property (count==0 |=> count==1);
  assert property (count==1 |=> count==2);
  assert property (count==2 |=> count==3);
  assert property (count==3 |=> count==4);
  assert property (count==4 |=> count==5);
  assert property (count==5 |=> count==6);
  assert property (count==6 |=> count==7);
  assert property (count==7 |=> count==0);

  // Output toggle policy
  assert property (count==7 |=> clk_1khz != $past(clk_1khz));     // must toggle on wrap
  assert property (count!=7 |=> clk_1khz == $past(clk_1khz));     // must hold otherwise
  assert property ((clk_1khz != $past(clk_1khz)) |-> $past(count)==7); // toggles only if prior count==7

  // Exact spacing between toggles: 8 input clocks
  assert property ((clk_1khz != $past(clk_1khz)) |-> $stable(clk_1khz)[*7] ##1 (clk_1khz != $past(clk_1khz)));

  // Coverage
  cover  property (count==0 ##1 count==1 ##1 count==2 ##1 count==3 ##1 count==4 ##1 count==5 ##1 count==6 ##1 count==7 ##1 count==0);
  cover  property ((clk_1khz != $past(clk_1khz)) ##1 $stable(clk_1khz)[*7] ##1 (clk_1khz != $past(clk_1khz)));
endmodule

bind clk_1_khz clk_1_khz_sva u_clk_1_khz_sva (.clk_50mhz(clk_50mhz), .clk_1khz(clk_1khz), .count(count));