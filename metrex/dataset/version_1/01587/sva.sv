// SVA for pmsm: normalize each input by subtracting the minimum; registered on clk
module pmsm_sva (
  input  logic        clk, reset,
  input  logic [3:0]  npm0, npm1, npm2, npm3,
  input  logic [3:0]  pm0,  pm1,  pm2,  pm3
);

  function automatic logic [3:0] min4 (input logic [3:0] a,b,c,d);
    logic [3:0] m;
    begin
      m = (a<=b)?a:b;
      m = (m<=c)?m:c;
      min4 = (m<=d)?m:d;
    end
  endfunction

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset)

  // Reset behavior
  a_reset_zero:  assert property (reset |-> (pm0==4'd0 && pm1==4'd0 && pm2==4'd0 && pm3==4'd0));
  a_reset_hold:  assert property (reset && $past(reset) |-> $stable({pm0,pm1,pm2,pm3}));

  // Functional normalization (checked 1 cycle later to avoid NBA sampling ambiguity)
  a_norm_func: assert property (
    (pm0 == ($past(npm0) - $past(min4(npm0,npm1,npm2,npm3)))) &&
    (pm1 == ($past(npm1) - $past(min4(npm0,npm1,npm2,npm3)))) &&
    (pm2 == ($past(npm2) - $past(min4(npm0,npm1,npm2,npm3)))) &&
    (pm3 == ($past(npm3) - $past(min4(npm0,npm1,npm2,npm3))))
  );

  // The minimum of outputs must be zero
  a_min_zero: assert property (min4(pm0,pm1,pm2,pm3) == 4'd0);

  // Strict-minimum index yields only that index zero; others strictly positive
  a_strict_min0: assert property ($past(npm0<npm1 && npm0<npm2 && npm0<npm3) |-> (pm0==4'd0 && pm1>4'd0 && pm2>4'd0 && pm3>4'd0));
  a_strict_min1: assert property ($past(npm1<npm0 && npm1<npm2 && npm1<npm3) |-> (pm1==4'd0 && pm0>4'd0 && pm2>4'd0 && pm3>4'd0));
  a_strict_min2: assert property ($past(npm2<npm0 && npm2<npm1 && npm2<npm3) |-> (pm2==4'd0 && pm0>4'd0 && pm1>4'd0 && pm3>4'd0));
  a_strict_min3: assert property ($past(npm3<npm0 && npm3<npm1 && npm3<npm2) |-> (pm3==4'd0 && pm0>4'd0 && pm1>4'd0 && pm2>4'd0));

  // Pairwise difference preservation (mod-16 arithmetic)
  a_diff_preserve: assert property (
    {pm0 - pm1, pm0 - pm2, pm0 - pm3} ==
    {$past(npm0 - npm1), $past(npm0 - npm2), $past(npm0 - npm3)}
  );

  // Coverage: each min case, ties, and all equal
  c_min0: cover property (npm0<=npm1 && npm0<=npm2 && npm0<=npm3);
  c_min1: cover property (npm1<=npm0 && npm1<=npm2 && npm1<=npm3);
  c_min2: cover property (npm2<=npm0 && npm2<=npm1 && npm2<=npm3);
  c_min3: cover property (npm3<=npm0 && npm3<=npm1 && npm3<=npm2);

  c_tie01: cover property ((npm0==npm1) && (npm0<=npm2) && (npm0<=npm3));
  c_tie012: cover property ((npm0==npm1) && (npm1==npm2) && (npm2<=npm3));
  c_all_equal: cover property (npm0==npm1 && npm1==npm2 && npm2==npm3);

endmodule

// Bind into DUT
bind pmsm pmsm_sva sva_i (.*);