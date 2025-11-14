// SVA for adder_tree_top
// Bind into DUT without modifying it
bind adder_tree_top adder_tree_top_sva sva_inst();

module adder_tree_top_sva;
  // default clock
  default clocking cb @(posedge clk); endclocking

  // basic init for $past usage
  bit init;
  always @(posedge clk) init <= 1'b1;

  // Structural/width sanity (elaboration time)
  initial begin
    assert ($bits(sum)       == `ADDER_WIDTH+1);
    assert ($bits(sum0)      == `ADDER_WIDTH+3);
    assert ($bits(sum0_0)    == `ADDER_WIDTH+2);
    assert ($bits(sum0_1)    == `ADDER_WIDTH+2);
    assert ($bits(sum0_0_0)  == `ADDER_WIDTH+1);
    assert ($bits(sum0_0_1)  == `ADDER_WIDTH+1);
    assert ($bits(sum0_1_0)  == `ADDER_WIDTH+1);
    assert ($bits(sum0_1_1)  == `ADDER_WIDTH+1);
    assert ($bits(sum0_0_0_0)== `ADDER_WIDTH);
    assert ($bits(sum0_0_0_1)== `ADDER_WIDTH);
    assert ($bits(sum0_0_1_0)== `ADDER_WIDTH);
    assert ($bits(sum0_0_1_1)== `ADDER_WIDTH);
    assert ($bits(sum0_1_0_0)== `ADDER_WIDTH);
    assert ($bits(sum0_1_0_1)== `ADDER_WIDTH);
    assert ($bits(sum0_1_1_0)== `ADDER_WIDTH);
    assert ($bits(sum0_1_1_1)== `ADDER_WIDTH);
  end

  // No X/Z on key state after first cycle
  assert property (init |-> !$isunknown({sum,
                                         sum0_0_0_0,sum0_0_0_1,sum0_0_1_0,sum0_0_1_1,
                                         sum0_1_0_0,sum0_1_0_1,sum0_1_1_0,sum0_1_1_1}));

  // Pipeline capture from inputs to stage-3 regs (1-cycle latency)
  assert property (disable iff (!init)
                   sum0_0_0_0 == $past(isum0_0_0_0) &&
                   sum0_0_0_1 == $past(isum0_0_0_1) &&
                   sum0_0_1_0 == $past(isum0_0_1_0) &&
                   sum0_0_1_1 == $past(isum0_0_1_1) &&
                   sum0_1_0_0 == $past(isum0_1_0_0) &&
                   sum0_1_0_1 == $past(isum0_1_0_1) &&
                   sum0_1_1_0 == $past(isum0_1_1_0) &&
                   sum0_1_1_1 == $past(isum0_1_1_1));

  // Level-3 adders (combinational correctness)
  assert property (sum0_0_0 == sum0_0_0_0 + sum0_0_0_1);
  assert property (sum0_0_1 == sum0_0_1_0 + sum0_0_1_1);
  assert property (sum0_1_0 == sum0_1_0_0 + sum0_1_0_1);
  assert property (sum0_1_1 == sum0_1_1_0 + sum0_1_1_1);

  // Level-2 adders (combinational correctness)
  assert property (sum0_0 == sum0_0_0 + sum0_0_1);
  assert property (sum0_1 == sum0_1_0 + sum0_1_1);

  // Level-1 adder (combinational correctness)
  assert property (sum0 == sum0_0 + sum0_1);

  // Output register mapping (1-cycle latency, with truncation to sum width)
`ifdef 2_LEVEL_ADDER
  assert property (disable iff (!init)
                   sum == $past(sum0_0[`ADDER_WIDTH:0]));
`elsif 3_LEVEL_ADDER
  assert property (disable iff (!init)
                   sum == $past(sum0[`ADDER_WIDTH:0]));
`endif

  // End-to-end from inputs (previous cycle) to current sum (truncated appropriately)
`ifdef 2_LEVEL_ADDER
  assert property (disable iff (!init)
                   sum == (( {1'b0,$past(isum0_0_0_0)} + {1'b0,$past(isum0_0_0_1)} ) +
                           ( {1'b0,$past(isum0_0_1_0)} + {1'b0,$past(isum0_0_1_1)} ))[`ADDER_WIDTH:0]);
`elsif 3_LEVEL_ADDER
  assert property (disable iff (!init)
                   sum == ((( {1'b0,$past(isum0_0_0_0)} + {1'b0,$past(isum0_0_0_1)} ) +
                            ( {1'b0,$past(isum0_0_1_0)} + {1'b0,$past(isum0_0_1_1)} )) +
                           (( {1'b0,$past(isum0_1_0_0)} + {1'b0,$past(isum0_1_0_1)} ) +
                            ( {1'b0,$past(isum0_1_1_0)} + {1'b0,$past(isum0_1_1_1)} )))[`ADDER_WIDTH:0]);
`endif

  // Functional coverage
  // Carry generation at each level
  cover property (sum0_0_0[`ADDER_WIDTH] == 1);
  cover property (sum0_0_1[`ADDER_WIDTH] == 1);
  cover property (sum0_1_0[`ADDER_WIDTH] == 1);
  cover property (sum0_1_1[`ADDER_WIDTH] == 1);
  cover property (sum0_0[`ADDER_WIDTH+1] == 1);
  cover property (sum0_1[`ADDER_WIDTH+1] == 1);
  cover property (sum0[`ADDER_WIDTH+2]   == 1);

  // Truncation/overflow observed at the selected output level
`ifdef 2_LEVEL_ADDER
  cover property (disable iff (!init) $past(sum0_0[`ADDER_WIDTH+1]) == 1 && sum == $past(sum0_0[`ADDER_WIDTH:0]));
`elsif 3_LEVEL_ADDER
  cover property (disable iff (!init) $past(sum0[`ADDER_WIDTH+2])   == 1 && sum == $past(sum0[`ADDER_WIDTH:0]));
`endif

  // All-zero and all-ones input patterns (previous cycle)
  cover property (disable iff (!init)
                  { $past(isum0_0_0_0),$past(isum0_0_0_1),$past(isum0_0_1_0),$past(isum0_0_1_1),
                    $past(isum0_1_0_0),$past(isum0_1_0_1),$past(isum0_1_1_0),$past(isum0_1_1_1)} == '0);

  cover property (disable iff (!init)
                  { $past(isum0_0_0_0),$past(isum0_0_0_1),$past(isum0_0_1_0),$past(isum0_0_1_1),
                    $past(isum0_1_0_0),$past(isum0_1_0_1),$past(isum0_1_1_0),$past(isum0_1_1_1)} ==
                  {8{ {`ADDER_WIDTH{1'b1}} }});
endmodule