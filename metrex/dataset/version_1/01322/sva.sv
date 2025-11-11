// SVA for adder_tree_top
// Bind-in so we can see internals; concise, high-signal-quality checks and coverage
module adder_tree_top_sva;

  // Use DUT clock
  default clocking cb @(posedge clk); endclocking

  bit past_valid;
  initial past_valid = 0;
  always @(posedge clk) past_valid <= 1'b1;

  // Static width sanity (compile-time) checks
  initial begin
    assert ($bits(sum)     == (`ADDER_WIDTH+1)) else $error("sum width != ADDER_WIDTH+1");
    assert ($bits(sum0)    == (`ADDER_WIDTH+3)) else $error("sum0 width != ADDER_WIDTH+3");
    assert ($bits(sum0_0)  == (`ADDER_WIDTH+2)) else $error("sum0_0/1 width != ADDER_WIDTH+2");
    assert ($bits(sum0_0_0)== (`ADDER_WIDTH+1)) else $error("sum0_0_* width != ADDER_WIDTH+1");
  end

  // Leaf register capture: 1-cycle latency from inputs to leaf regs
  assert property (disable iff(!past_valid) sum0_0_0_0 == $past(isum0_0_0_0));
  assert property (disable iff(!past_valid) sum0_0_0_1 == $past(isum0_0_0_1));
  assert property (disable iff(!past_valid) sum0_0_1_0 == $past(isum0_0_1_0));
  assert property (disable iff(!past_valid) sum0_0_1_1 == $past(isum0_0_1_1));
  assert property (disable iff(!past_valid) sum0_1_0_0 == $past(isum0_1_0_0));
  assert property (disable iff(!past_valid) sum0_1_0_1 == $past(isum0_1_0_1));
  assert property (disable iff(!past_valid) sum0_1_1_0 == $past(isum0_1_1_0));
  assert property (disable iff(!past_valid) sum0_1_1_1 == $past(isum0_1_1_1));

  // Combinational correctness of each adder branch
  assert property ((!$isunknown({sum0_0_0_0,sum0_0_0_1})) |-> sum0_0_0 == sum0_0_0_0 + sum0_0_0_1);
  assert property ((!$isunknown({sum0_0_1_0,sum0_0_1_1})) |-> sum0_0_1 == sum0_0_1_0 + sum0_0_1_1);
  assert property ((!$isunknown({sum0_1_0_0,sum0_1_0_1})) |-> sum0_1_0 == sum0_1_0_0 + sum0_1_0_1);
  assert property ((!$isunknown({sum0_1_1_0,sum0_1_1_1})) |-> sum0_1_1 == sum0_1_1_0 + sum0_1_1_1);

  assert property ((!$isunknown({sum0_0_0,sum0_0_1})) |-> sum0_0 == sum0_0_0 + sum0_0_1);
  assert property ((!$isunknown({sum0_1_0,sum0_1_1})) |-> sum0_1 == sum0_1_0 + sum0_1_1);

  assert property ((!$isunknown({sum0_0,sum0_1})) |-> sum0 == sum0_0 + sum0_1);

  // End-to-end latency and truncation-equivalence at the top-level output
  `ifdef 3_LEVEL_ADDER
    // sum is registered truncated view of sum0
    assert property (disable iff(!past_valid)
                     !$isunknown($past(sum0[`ADDER_WIDTH:0])) |-> sum == $past(sum0[`ADDER_WIDTH:0]));

    // Cover any non-zero truncated bits (would indicate information loss)
    cover property (disable iff(!past_valid)
                    !$isunknown($past(sum0)) && (|$past(sum0[`ADDER_WIDTH+2:`ADDER_WIDTH+1])));
  `endif

  `ifdef 2_LEVEL_ADDER
    assert property (disable iff(!past_valid)
                     !$isunknown($past(sum0_0[`ADDER_WIDTH:0])) |-> sum == $past(sum0_0[`ADDER_WIDTH:0]));

    cover property (disable iff(!past_valid)
                    !$isunknown($past(sum0_0)) && $past(sum0_0[`ADDER_WIDTH+1]));
  `endif

  // Output known if prior-cycle inputs were known
  assert property (disable iff(!past_valid)
                   !$isunknown($past({
                     isum0_0_0_0,isum0_0_0_1,isum0_0_1_0,isum0_0_1_1,
                     isum0_1_0_0,isum0_1_0_1,isum0_1_1_0,isum0_1_1_1
                   })) |-> !$isunknown(sum));

  // Coverage: exercise carries at each level
  cover property (!$isunknown({sum0_0_0_0,sum0_0_0_1}) && sum0_0_0[`ADDER_WIDTH]);
  cover property (!$isunknown({sum0_0_1_0,sum0_0_1_1}) && sum0_0_1[`ADDER_WIDTH]);
  cover property (!$isunknown({sum0_1_0_0,sum0_1_0_1}) && sum0_1_0[`ADDER_WIDTH]);
  cover property (!$isunknown({sum0_1_1_0,sum0_1_1_1}) && sum0_1_1[`ADDER_WIDTH]);

  cover property (!$isunknown({sum0_0_0,sum0_0_1}) && sum0_0[`ADDER_WIDTH+1]);
  cover property (!$isunknown({sum0_1_0,sum0_1_1}) && sum0_1[`ADDER_WIDTH+1]);

  cover property (!$isunknown({sum0_0,sum0_1}) && sum0[`ADDER_WIDTH+2]);

endmodule

bind adder_tree_top adder_tree_top_sva sva_top();