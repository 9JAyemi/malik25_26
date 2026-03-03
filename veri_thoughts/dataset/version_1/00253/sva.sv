// SVA for two_bit_sat_counter
module two_bit_sat_counter_sva (
  input  [1:0] count_i,
  input        op,
  input  [1:0] count
);

  // Functional correctness (increment direction)
  property p_inc;
    op && !$isunknown(count_i) |->
      count ==
        (count_i==2'b00 ? 2'b01 :
         count_i==2'b01 ? 2'b10 :
         count_i==2'b10 ? 2'b10 :
                          2'b11);
  endproperty
  assert property (@(*) p_inc);

  // Functional correctness (decrement direction)
  property p_dec;
    !op && !$isunknown(count_i) |->
      count ==
        (count_i==2'b00 ? 2'b00 :
         count_i==2'b01 ? 2'b00 :
         count_i==2'b10 ? 2'b01 :
                          2'b10);
  endproperty
  assert property (@(*) p_dec);

  // Monotonicity (saturating behavior)
  assert property (@(*) (op  && !$isunknown(count_i)) |->
                           (count >= count_i));
  assert property (@(*) (!op && !$isunknown(count_i)) |->
                           (count <= count_i));

  // No X on output when inputs are known
  assert property (@(*) (!$isunknown({op,count_i})) |->
                           !$isunknown(count));

  // Functional coverage: all input/output combinations
  cover property (@(*) (count_i==2'b00 &&  op && count==2'b01));
  cover property (@(*) (count_i==2'b01 &&  op && count==2'b10));
  cover property (@(*) (count_i==2'b10 &&  op && count==2'b10));
  cover property (@(*) (count_i==2'b11 &&  op && count==2'b11));

  cover property (@(*) (count_i==2'b00 && !op && count==2'b00));
  cover property (@(*) (count_i==2'b01 && !op && count==2'b00));
  cover property (@(*) (count_i==2'b10 && !op && count==2'b01));
  cover property (@(*) (count_i==2'b11 && !op && count==2'b10));

endmodule

bind two_bit_sat_counter two_bit_sat_counter_sva sva_i (
  .count_i(count_i),
  .op(op),
  .count(count)
);