// SVA for xor_adder
module xor_adder_sva (
  input clk,
  input [1:0] a,
  input [1:0] b,
  input [1:0] sum,
  input [1:0] stage1_sum,
  input [1:0] stage2_sum
);

  bit past1, past2, past3;
  always @(posedge clk) begin
    past1 <= 1'b1;
    past2 <= past1;
    past3 <= past2;
  end

  // Pipeline correctness (cycle-accurate)
  // stage1_sum[n] = a[n-1] ^ b[n-1]
  assert property (@(posedge clk)
    past1 && !$isunknown($past({a,b})) |-> (stage1_sum === $past(a ^ b))
  );

  // stage2_sum[n] = stage1_sum[n-1] ^ sum[n-1]
  assert property (@(posedge clk)
    past1 && !$isunknown($past({stage1_sum,sum})) |-> (stage2_sum === ($past(stage1_sum) ^ $past(sum)))
  );

  // sum[n] = stage2_sum[n-1]
  assert property (@(posedge clk)
    past1 && !$isunknown($past(stage2_sum)) |-> (sum === $past(stage2_sum))
  );

  // Derived relations for redundancy/strength
  // stage2_sum[n] = a[n-2] ^ b[n-2] ^ sum[n-1]
  assert property (@(posedge clk)
    past2 && !$isunknown($past(a ^ b,2)) && !$isunknown($past(sum,1))
      |-> (stage2_sum === ($past(a ^ b,2) ^ $past(sum,1)))
  );

  // sum[n] = sum[n-2] ^ (a[n-3] ^ b[n-3])
  assert property (@(posedge clk)
    past3 && !$isunknown($past(sum,2)) && !$isunknown($past(a ^ b,3))
      |-> (sum === ($past(sum,2) ^ $past(a ^ b,3)))
  );

  // Change-correlation checks
  assert property (@(posedge clk)
    past1 && $changed(sum) |-> $changed($past(stage2_sum))
  );

  // Functional coverage
  cover property (@(posedge clk) stage1_sum == 2'b00);
  cover property (@(posedge clk) stage1_sum == 2'b01);
  cover property (@(posedge clk) stage1_sum == 2'b10);
  cover property (@(posedge clk) stage1_sum == 2'b11);

  cover property (@(posedge clk) past1 && stage2_sum === ($past(stage1_sum) ^ $past(sum)));
  cover property (@(posedge clk) past3 && sum === ($past(sum,2) ^ $past(a ^ b,3)));

  cover property (@(posedge clk) $changed(stage1_sum));
  cover property (@(posedge clk) $changed(stage2_sum));
  cover property (@(posedge clk) $changed(sum));

endmodule

bind xor_adder xor_adder_sva sva_xor_adder (.*);