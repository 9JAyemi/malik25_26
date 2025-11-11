// SVA for three_input_three_output
module three_input_three_output_sva
(
  input i_0r,
  input reset,
  input o_0a,
  input o_1a,
  input i_0a,
  input o_0r,
  input o_1r
);

  // Async reset: immediate clear and hold-low while reset=1
  assert property (@(posedge reset) ##0 (!i_0a && !o_0r && !o_1r));
  assert property (@(posedge i_0r) reset |-> (!i_0a && !o_0r && !o_1r));

  // Inputs known at sampling; outputs known after update
  assert property (@(posedge i_0r) !$isunknown({o_0a,o_1a,reset}));
  assert property (@(posedge i_0r) disable iff(reset) 1 |-> ##0 !$isunknown({i_0a,o_0r,o_1r}));

  // Request replicated to both outputs in the same cycle; outputs equal
  assert property (@(posedge i_0r) disable iff(reset) 1 |-> ##0 (o_0r && o_1r));
  assert property (@(posedge i_0r) disable iff(reset) (o_0r == o_1r));

  // i_0a updates to AND of downstream acks in the same cycle
  assert property (@(posedge i_0r) disable iff(reset) 1 |-> ##0 (i_0a == (o_0a && o_1a)));

  // o_*r are sticky high while reset=0 (no falling edges)
  assert property (@(posedge i_0r) disable iff(reset) !$fell(o_0r));
  assert property (@(posedge i_0r) disable iff(reset) !$fell(o_1r));

  // Coverage
  cover property (@(posedge i_0r) !reset &&  o_0a &&  o_1a ##0 (i_0a && o_0r && o_1r));
  cover property (@(posedge i_0r) !reset && (!o_0a || !o_1a) ##0 (!i_0a && o_0r && o_1r));
  cover property (@(posedge i_0r) !reset ##1 !reset ##1 !reset); // multiple ticks while not in reset
  cover property (@(posedge reset) ##0 (!i_0a && !o_0r && !o_1r));

endmodule

bind three_input_three_output three_input_three_output_sva
(
  .i_0r (i_0r),
  .reset(reset),
  .o_0a (o_0a),
  .o_1a (o_1a),
  .i_0a (i_0a),
  .o_0r (o_0r),
  .o_1r (o_1r)
);