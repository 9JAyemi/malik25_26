// SVA for barrel_shifter
// Bind into DUT; checks correctness, detects dead branch, and provides concise coverage.

module barrel_shifter_sva
(
  input  logic [3:0] data_in,
  input  logic [1:0] shift_amount,
  input  logic       mode,
  input  logic [3:0] data_out
);

  // On every posedge of mode, data_out must reflect left shift (else-branch is always taken)
  property p_left_shift_on_rose_mode;
    @(posedge mode) ##0 (data_out == (data_in << shift_amount));
  endproperty
  assert property (p_left_shift_on_rose_mode)
    else $error("barrel_shifter: data_out != (data_in << shift_amount) at posedge mode");

  // Sanity: posedge(mode) must sample mode==1 (the if(mode==0) branch is unreachable)
  property p_posedge_mode_is_one;
    @(posedge mode) mode;
  endproperty
  assert property (p_posedge_mode_is_one)
    else $error("barrel_shifter: sampled mode==0 on its posedge (unreachable branch)");

  // No unintended updates: data_out may only change coincident with a posedge of mode
  property p_out_changes_only_with_rose_mode;
    @(posedge mode or negedge mode
      or posedge data_in[0] or negedge data_in[0]
      or posedge data_in[1] or negedge data_in[1]
      or posedge data_in[2] or negedge data_in[2]
      or posedge data_in[3] or negedge data_in[3]
      or posedge shift_amount[0] or negedge shift_amount[0]
      or posedge shift_amount[1] or negedge shift_amount[1])
      (!$rose(mode)) |-> ##0 $stable(data_out);
  endproperty
  assert property (p_out_changes_only_with_rose_mode)
    else $error("barrel_shifter: data_out changed without posedge mode");

  // Knownness: if inputs are known at posedge, the latched output must be known
  property p_known_on_rose_mode;
    @(posedge mode) (!$isunknown({data_in, shift_amount, mode})) |-> ##0 (!$isunknown(data_out));
  endproperty
  assert property (p_known_on_rose_mode)
    else $error("barrel_shifter: X/Z propagated to data_out at posedge mode");

  // Coverage
  cover property (@(posedge mode) 1);                       // observe at least one update
  cover property (@(posedge mode) shift_amount == 2'd0);
  cover property (@(posedge mode) shift_amount == 2'd1);
  cover property (@(posedge mode) shift_amount == 2'd2);
  cover property (@(posedge mode) shift_amount == 2'd3);
  // Dead-code indicator (should never hit): if-branch on mode==0 inside posedge-mode block
  cover property (@(posedge mode) mode == 1'b0);

endmodule

bind barrel_shifter barrel_shifter_sva i_barrel_shifter_sva
(
  .data_in      (data_in),
  .shift_amount (shift_amount),
  .mode         (mode),
  .data_out     (data_out)
);