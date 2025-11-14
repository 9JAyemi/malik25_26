// SVA for adder_4_2. Bind this checker to the DUT.

module adder_4_2_sva (
  input  logic [3:0] A,
  input  logic [1:0] Y,
  input  logic [2:0] sum,
  input  logic [1:0] constant
);
  let s3 = (A + {2'b00, constant})[2:0];

  a_const_fixed: assert property (constant === 2'b10);
  a_sum_trunc:   assert property (sum === s3);
  a_y_saturate:  assert property (Y   === (s3[2] ? 2'b11 : s3[1:0]));

  a_no_x:        assert property ((!$isunknown(A) && !$isunknown(constant))
                                  |-> (!$isunknown(sum) && !$isunknown(Y)));

  // Coverage
  c_pass_through: cover property (!s3[2] && Y == s3[1:0]);
  c_saturated:    cover property ( s3[2] && Y == 2'b11);
  c_boundary3:    cover property (s3 == 3 && Y == 2'b11);
  c_boundary4:    cover property (s3 == 4 && Y == 2'b11);
  c_y_00:         cover property (Y == 2'b00);
  c_y_01:         cover property (Y == 2'b01);
  c_y_10:         cover property (Y == 2'b10);
  c_y_11:         cover property (Y == 2'b11);
endmodule

bind adder_4_2 adder_4_2_sva sva(.A(A), .Y(Y), .sum(sum), .constant(constant));