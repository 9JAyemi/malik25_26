// SVA checker for pipelined_circuit. Bind this to the DUT.
// Focused, concise, and covers functionality, consistency, and key coverage.

module pc_sva (
  input  logic [3:0] in,
  input  logic       out_and,
  input  logic       out_or,
  input  logic       out_xor,
  input  logic [3:0] stage1_out,
  input  logic [2:0] stage2_out
);

  // Stage 1 functional correctness
  assert property (@(*)) stage1_out[0] === (in[0] & in[1]);
  assert property (@(*)) stage1_out[1] === (in[2] & in[3]);
  assert property (@(*)) stage1_out[2] === (stage1_out[0] | stage1_out[1]);
  assert property (@(*)) stage1_out[3] === (stage1_out[0] ^ stage1_out[1]);

  // Stage 2 functional correctness
  assert property (@(*)) stage2_out[0] === (stage1_out[0] & stage1_out[1]); // AND
  assert property (@(*)) stage2_out[1] === (stage1_out[2] | stage1_out[3]); // OR
  assert property (@(*)) stage2_out[2] === (stage1_out[2] ^ stage1_out[3]); // XOR

  // Output mapping correctness
  assert property (@(*)) out_and === stage2_out[0];
  assert property (@(*)) out_or  === stage2_out[1];
  assert property (@(*)) out_xor === stage2_out[2];

  // End-to-end correctness from inputs
  assert property (@(*)) out_and === ((in[0]&in[1]) & (in[2]&in[3]));
  assert property (@(*)) out_or  === (((in[0]&in[1]) | (in[2]&in[3])) | ((in[0]&in[1]) ^ (in[2]&in[3])));
  assert property (@(*)) out_xor === (((in[0]&in[1]) | (in[2]&in[3])) ^ ((in[0]&in[1]) ^ (in[2]&in[3])));

  // X-propagation sanity: known inputs imply known internals/outputs
  assert property (@(*)) (!$isunknown(in)) |-> (!$isunknown({stage1_out,stage2_out,out_and,out_or,out_xor}));

  // Logical consistency implications
  // XOR implies OR (for both stages)
  assert property (@(*)) stage1_out[3] |->  stage1_out[2];
  assert property (@(*)) stage2_out[2] |->  stage2_out[1];
  // AND vs XOR mutual exclusion at stage boundary
  assert property (@(*)) stage2_out[0] |-> (stage1_out[2] && !stage1_out[3]);
  assert property (@(*)) stage1_out[3] |-> !stage2_out[0];

  // Combinational stability: stable inputs => stable internals/outputs
  assert property (@(*)) $stable(in) |-> $stable({stage1_out,stage2_out,out_and,out_or,out_xor});

  // Coverage: exercise OR/XOR quadrant at stage 1
  cover property (@(*)) (stage1_out[2]==0 && stage1_out[3]==0);
  cover property (@(*)) (stage1_out[2]==0 && stage1_out[3]==1);
  cover property (@(*)) (stage1_out[2]==1 && stage1_out[3]==0);
  cover property (@(*)) (stage1_out[2]==1 && stage1_out[3]==1);

  // Coverage: each output can assert and toggle
  cover property (@(*)) out_and;
  cover property (@(*)) out_or;
  cover property (@(*)) out_xor;

  cover property (@(*)) $rose(out_and));
  cover property (@(*)) $fell(out_and));
  cover property (@(*)) $rose(out_or));
  cover property (@(*)) $fell(out_or));
  cover property (@(*)) $rose(out_xor));
  cover property (@(*)) $fell(out_xor));

endmodule

// Bind into DUT (accesses internal nets stage1_out/stage2_out)
bind pipelined_circuit pc_sva pc_sva_i (
  .in(in),
  .out_and(out_and),
  .out_or(out_or),
  .out_xor(out_xor),
  .stage1_out(stage1_out),
  .stage2_out(stage2_out)
);