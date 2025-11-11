// SVA for sequence_counter
// Bind this module to the DUT to check functionality and provide coverage.
module sequence_counter_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic [9:0]  data,
  input  logic [2:0]  seq,
  input  logic [3:0]  cnt,
  input  logic [3:0]  count
);

  // Synchronous reset forces zeros
  property p_reset_zeros;
    @(posedge clk) reset |-> (seq == 3'b000 && cnt == 4'b0000);
  endproperty
  assert property (p_reset_zeros);

  // Exact seq update (shift in data[0]); handles post-reset cycle
  property p_seq_shift;
    @(posedge clk)
      !reset |-> seq ==
        ( $past(reset) ? {2'b00, $past(data[0])} : {$past(seq[1:0]), $past(data[0])} );
  endproperty
  assert property (p_seq_shift);

  // Count increments by +1 (with wrap) iff prior seq was 3'b101
  property p_inc_on_101;
    @(posedge clk) disable iff (reset)
      (!$past(reset) && $past(seq) == 3'b101)
      |-> (cnt == ($past(cnt) == 4'hF ? 4'h0 : $past(cnt) + 4'd1));
  endproperty
  assert property (p_inc_on_101);

  // No increment otherwise
  property p_hold_when_not_101;
    @(posedge clk) disable iff (reset)
      (!$past(reset) && $past(seq) != 3'b101)
      |-> (cnt == $past(cnt));
  endproperty
  assert property (p_hold_when_not_101);

  // Any change in cnt must be due to 3'b101
  property p_change_implies_101;
    @(posedge clk) disable iff (reset)
      (cnt != $past(cnt)) |-> (!$past(reset) && $past(seq) == 3'b101);
  endproperty
  assert property (p_change_implies_101);

  // No back-to-back increments on adjacent cycles
  property p_no_back_to_back_inc;
    @(posedge clk) disable iff (reset)
      (cnt != $past(cnt) && !$past(reset)) |=> (cnt == $past(cnt));
  endproperty
  assert property (p_no_back_to_back_inc);

  // Output mirrors internal counter
  property p_count_alias;
    @(posedge clk) (count == cnt);
  endproperty
  assert property (p_count_alias);

  // Coverage

  // See the 101 detection and increment
  cover property (@(posedge clk) disable iff (reset)
    (!$past(reset) && $past(seq) == 3'b101) && 
    (cnt == ($past(cnt) == 4'hF ? 4'h0 : $past(cnt) + 4'd1))
  );

  // See a wrap from 0xF -> 0x0 on a 101 detection
  cover property (@(posedge clk) disable iff (reset)
    ($past(seq) == 3'b101 && $past(cnt) == 4'hF && cnt == 4'h0)
  );

  // See first post-reset shift behavior
  cover property (@(posedge clk)
    ($past(reset) && !reset && seq == {2'b00, $past(data[0])})
  );

endmodule

// Bind into the DUT
bind sequence_counter sequence_counter_sva sva (
  .clk   (clk),
  .reset (reset),
  .data  (data),
  .seq   (seq),
  .cnt   (cnt),
  .count (count)
);