// SVA checker for rotator. Bind into DUT to access internals.
module rotator_sva (
  input logic        clk,
  input logic        load,
  input logic [1:0]  ena,
  input logic [99:0] data,
  input logic [99:0] q,
  input logic [99:0] stage1_data,
  input logic [99:0] stage2_data,
  input logic [99:0] stage3_data
);

  logic init_done;
  initial init_done = 1'b0;
  always @(posedge clk) init_done <= 1'b1;

  default clocking cb @(posedge clk); endclocking
  default disable iff (!init_done);

  // Basic knownness (avoid X/Z on controls; data known when used)
  assert property (!$isunknown({load, ena})); 
  assert property ( (load || (ena==2'b00)) |-> !$isunknown(data) );

  // Output mux correctness (observe after NBA updates)
  assert property (1'b1 |-> ##0 ( q == (ena==2'b00 ? data
                                        : ena==2'b01 ? stage1_data
                                        : ena==2'b10 ? stage2_data
                                                      : stage3_data) ));

  // Next-state: load has priority; pipeline load behavior
  assert property ( load |=> stage1_data == $past(data)
                           && stage2_data == $past(stage1_data)
                           && stage3_data == $past(stage2_data) );

  // Next-state: left rotation when ena==01 and not loading
  assert property ( !load && ena==2'b01 |=> 
                      stage1_data == { $past(stage1_data)[98:0], $past(stage1_data)[99] } &&
                      stage2_data == { $past(stage2_data)[97:0], $past(stage2_data)[99:98] } &&
                      stage3_data == { $past(stage3_data)[96:0], $past(stage3_data)[99:97] } );

  // Next-state: right rotation when ena==10 and not loading
  assert property ( !load && ena==2'b10 |=> 
                      stage1_data == { $past(stage1_data)[1:99],  $past(stage1_data)[0] } &&
                      stage2_data == { $past(stage2_data)[2:99],  $past(stage2_data)[1:0] } &&
                      stage3_data == { $past(stage3_data)[3:99],  $past(stage3_data)[2:0] } );

  // Next-state: hold when neither load nor rotate branches taken (ena==00 or 11)
  assert property ( !load && !(ena==2'b01) && !(ena==2'b10) |=> 
                      stage1_data == $past(stage1_data) &&
                      stage2_data == $past(stage2_data) &&
                      stage3_data == $past(stage3_data) );

  // Covers: exercise all control paths and mux selections
  cover property (load);
  cover property (!load && ena==2'b00);
  cover property (!load && ena==2'b01);
  cover property (!load && ena==2'b10);
  cover property (!load && ena==2'b11);

  cover property ( (ena==2'b01) ##1 (ena==2'b10) ); // left then right
  cover property ( (ena==2'b10) ##1 (ena==2'b01) ); // right then left

  // Wrap-around covers: after 100 consecutive rotations, stage1 returns
  cover property ( !load && ena==2'b01 [*100] ##1 stage1_data == $past(stage1_data,101) );
  cover property ( !load && ena==2'b10 [*100] ##1 stage1_data == $past(stage1_data,101) );

endmodule

// Bind into DUT to access internals
bind rotator rotator_sva rotator_sva_i (
  .clk(clk),
  .load(load),
  .ena(ena),
  .data(data),
  .q(q),
  .stage1_data(stage1_data),
  .stage2_data(stage2_data),
  .stage3_data(stage3_data)
);