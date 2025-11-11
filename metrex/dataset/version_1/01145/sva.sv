// SVA for rotator: concise, full next-state checking, priorities, holds, connectivity, and coverage.
`ifndef SYNTHESIS
module rotator_sva;
  default clocking cb @(posedge clk); endclocking

  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  // Basic sanity
  assert property (cb ! $isunknown({load, ena}));
  assert property (cb past_valid |-> ! $isunknown(q));
  // Connectivity
  assert property (cb q == pipeline_reg[0]);

  // Load has highest priority
  assert property (cb past_valid && $past(load) |-> 
      pipeline_reg[0] == $past(data) &&
      pipeline_reg[1] == '0 &&
      pipeline_reg[2] == '0);

  // ena == 2'b01 update
  assert property (cb past_valid && !$past(load) && $past(ena)==2'b01 |-> 
      pipeline_reg[0] == {$past(pipeline_reg[0][98:0]), $past(pipeline_reg[2][0])} &&
      pipeline_reg[1] == $past(pipeline_reg[0]) &&
      pipeline_reg[2] == {$past(pipeline_reg[2][98:0]), $past(pipeline_reg[0][0])});

  // ena == 2'b10 update
  assert property (cb past_valid && !$past(load) && $past(ena)==2'b10 |-> 
      pipeline_reg[0] == {$past(pipeline_reg[1][98:1]), $past(pipeline_reg[0][0])} &&
      pipeline_reg[1] == {$past(pipeline_reg[2][98:1]), $past(pipeline_reg[1][0])} &&
      pipeline_reg[2] == $past(pipeline_reg[2]));

  // Hold when ena==00 or 11 (no load)
  assert property (cb past_valid && !$past(load) && ($past(ena)==2'b00 || $past(ena)==2'b11) |-> 
      pipeline_reg[0] == $past(pipeline_reg[0]) &&
      pipeline_reg[1] == $past(pipeline_reg[1]) &&
      pipeline_reg[2] == $past(pipeline_reg[2]));

  // Coverage: all control cases + key data movements
  cover property (cb load);
  cover property (cb !load && ena==2'b01);
  cover property (cb !load && ena==2'b10);
  cover property (cb !load && (ena==2'b00 || ena==2'b11));
  cover property (cb past_valid && $past(load) && (pipeline_reg[0]==$past(data)));
  cover property (cb past_valid && !$past(load) && $past(ena)==2'b01 &&
                  pipeline_reg[0][0] == $past(pipeline_reg[2][0]) &&
                  pipeline_reg[2][0] == $past(pipeline_reg[0][0]));
  cover property (cb past_valid && !$past(load) && $past(ena)==2'b10 &&
                  pipeline_reg[2] == $past(pipeline_reg[2]) &&
                  pipeline_reg[0][0] == $past(pipeline_reg[0][0]) &&
                  pipeline_reg[1][0] == $past(pipeline_reg[1][0]));
endmodule

bind rotator rotator_sva rotator_sva_i();
`endif