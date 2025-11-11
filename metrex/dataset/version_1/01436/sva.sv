// SVA checker for module magnitude (bind this into your DUT instance)
// Example bind (provide your clock/reset):
// bind magnitude magnitude_sva #(12) u_mag_sva (.clk(clk), .rst_n(rst_n));

module magnitude_sva #(parameter int W=12) (
  input logic clk,
  input logic rst_n
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // No X/Z on key signals
  a_no_x: assert property (
    !$isunknown({Y0,Y1,Y2,Y3,Z0,Z1,Z2,Z3,max1,max2,min1,min2,mag1,mag2})
  );

  // toPositive correctness for all legs
  property p_to_pos (logic [W-1:0] in, logic [W-1:0] out);
    out == (in[W-1] ? ((~in) + 1) : in);
  endproperty
  a_topos0: assert property (p_to_pos(Y0, Z0));
  a_topos1: assert property (p_to_pos(Y1, Z1));
  a_topos2: assert property (p_to_pos(Y2, Z2));
  a_topos3: assert property (p_to_pos(Y3, Z3));

  // max/min correctness (pair Y0/Y1 -> Z0/Z1, pair Y2/Y3 -> Z2/Z3)
  a_max1_hi: assert property ( (Z1 > Z0) |-> (max1 == Z1) );
  a_max1_lo: assert property ( (Z1 <= Z0) |-> (max1 == Z0) );
  a_min1_hi: assert property ( (Z1 > Z0) |-> (min1 == Z0) );
  a_min1_lo: assert property ( (Z1 <= Z0) |-> (min1 == Z1) );

  a_max2_hi: assert property ( (Z3 > Z2) |-> (max2 == Z3) );
  a_max2_lo: assert property ( (Z3 <= Z2) |-> (max2 == Z2) );
  a_min2_hi: assert property ( (Z3 > Z2) |-> (min2 == Z2) );
  a_min2_lo: assert property ( (Z3 <= Z2) |-> (min2 == Z3) );

  // Consistency: ranges and source-of-results
  a_mm1_rel: assert property (min1 <= max1);
  a_mm2_rel: assert property (min2 <= max2);
  a_max_is_input1: assert property ( (max1 == Z0) || (max1 == Z1) );
  a_max_is_input2: assert property ( (max2 == Z2) || (max2 == Z3) );
  a_min_is_input1: assert property ( (min1 == Z0) || (min1 == Z1) );
  a_min_is_input2: assert property ( (min2 == Z2) || (min2 == Z3) );

  // Magnitude arithmetic
  a_mag1_eq: assert property ( mag1 == (max1 + (min1 >> 2) - (max1 >> 4)) );
  a_mag2_eq: assert property ( mag2 == (max2 + (min2 >> 2) - (max2 >> 4)) );

  // Magnitude bounds (derived from formula)
  a_mag1_lb: assert property ( mag1 >= (max1 - (max1 >> 4)) );
  a_mag1_ub: assert property ( mag1 <= (max1 + (min1 >> 2)) );
  a_mag2_lb: assert property ( mag2 >= (max2 - (max2 >> 4)) );
  a_mag2_ub: assert property ( mag2 <= (max2 + (min2 >> 2)) );

  // Coverage: toPositive sign cases (incl. -2^(W-1))
  c_pos0_neg:    cover property ( Y0[W-1] && (Y0 != {1'b1,{(W-1){1'b0}}}) );
  c_pos0_minneg: cover property ( Y0 == {1'b1,{(W-1){1'b0}}} );
  c_pos0_pos:    cover property ( !Y0[W-1] );
  c_pos1_neg:    cover property ( Y1[W-1] );
  c_pos2_neg:    cover property ( Y2[W-1] );
  c_pos3_neg:    cover property ( Y3[W-1] );

  // Coverage: compare outcomes
  c_cmp1_gt: cover property (Z1 > Z0);
  c_cmp1_eq: cover property (Z1 == Z0);
  c_cmp1_lt: cover property (Z1 < Z0);
  c_cmp2_gt: cover property (Z3 > Z2);
  c_cmp2_eq: cover property (Z3 == Z2);
  c_cmp2_lt: cover property (Z3 < Z2);

  // Coverage: representative extreme patterns
  c_all_zero: cover property ({Y0,Y1,Y2,Y3} == '0);
  c_extremes: cover property (
    (Y0 == {1'b0,{(W-1){1'b1}}}) && // +max
    (Y1 == {W{1'b1}})            && // -1
    (Y2 == {1'b1,{(W-1){1'b0}}}) && // -2^(W-1)
    (Y3 == '0)
  );
endmodule