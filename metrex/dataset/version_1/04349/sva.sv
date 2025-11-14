// SVA for mag_comparator
// Bind this file to the DUT
bind mag_comparator mag_comparator_sva i_mag_comparator_sva(.A(A), .B(B), .result(result));

module mag_comparator_sva(
  input logic [2:0] A,
  input logic [2:0] B,
  input logic [1:0] result
);

  function automatic logic [1:0] exp_result (logic [2:0] a, b);
    return (a==b) ? 2'b00 : (a>b) ? 2'b01 : 2'b10;
  endfunction

  // Core equivalence (covers all cases)
  ap_equiv: assert property (@(A or B or result) ##0 (result === exp_result(A,B)));

  // Sanity (legal encoding and no X/Z on result)
  ap_legal: assert property (@(A or B or result) ##0 (result inside {2'b00,2'b01,2'b10} && !$isunknown(result)));

  // Directional consistency (helpful for debug)
  ap_eq:  assert property (@(A or B or result) ##0 ((A==B)  |-> (result==2'b00)));
  ap_gt:  assert property (@(A or B or result) ##0 ((A>B)   |-> (result==2'b01)));
  ap_lt:  assert property (@(A or B or result) ##0 ((A<B)   |-> (result==2'b10)));
  ap_eq_r: assert property (@(A or B or result) ##0 ((result==2'b00) |-> (A==B)));
  ap_gt_r: assert property (@(A or B or result) ##0 ((result==2'b01) |-> (A>B)));
  ap_lt_r: assert property (@(A or B or result) ##0 ((result==2'b10) |-> (A<B)));

  // Functional coverage: all three outcomes and useful extremes
  cover_eq: cover property (@(A or B) ##0 (A==B  && result==2'b00));
  cover_gt: cover property (@(A or B) ##0 (A>B   && result==2'b01));
  cover_lt: cover property (@(A or B) ##0 (A<B   && result==2'b10));

  cover_minmax1: cover property (@(A or B) ##0 (A==3'd0 && B==3'd7 && result==2'b10));
  cover_minmax2: cover property (@(A or B) ##0 (A==3'd7 && B==3'd0 && result==2'b01));
  cover_zeros:   cover property (@(A or B) ##0 (A==3'd0 && B==3'd0 && result==2'b00));
  cover_ones:    cover property (@(A or B) ##0 (A==3'd7 && B==3'd7 && result==2'b00));

endmodule