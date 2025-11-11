// SVA for comparator_8bit

module comparator_8bit_sva;
  // Bound into DUT scope; can see in1, in2, match, temp
  default clocking cb @(in1 or in2 or match or temp); endclocking

  // Functional correctness (4-state accurate)
  assert property (match === &(in1 ~^ in2));

  // Internal staging correctness
  assert property (temp === (in1 ~^ in2));

  // Known inputs => match is known and equals 2-state equality
  assert property (!$isunknown({in1, in2}) |-> (match !== 1'bx && match == (in1 == in2)));

  // Coverage
  cover property (!$isunknown({in1, in2}) && (in1 == in2) && (match == 1));
  cover property (!$isunknown({in1, in2}) && (in1 != in2) && (match == 0));
  cover property ($isunknown({in1, in2}) && match === 1'bx);

  genvar i;
  generate
    for (i = 0; i < 8; i++) begin : per_bit_cov
      cover property (!$isunknown({in1[i], in2[i]}) && (in1[i] != in2[i]) |-> (match == 0));
    end
  endgenerate
endmodule

bind comparator_8bit comparator_8bit_sva sva();