// SVA checker for mux4_diff
module mux4_diff_sva (
    input logic [3:0] I,
    input logic [1:0] S,
    input logic       O,
    input logic       OB
);
  default clocking cb @(*); endclocking

  // Functional correctness per select value (guards avoid X on inputs)
  assert property ( (S === 2'b00 && !$isunknown(I[0])) |-> (O === I[0] && OB === ~I[0]) );
  assert property ( (S === 2'b01 && !$isunknown(I[1])) |-> (O === I[1] && OB === ~I[1]) );
  assert property ( (S === 2'b10 && !$isunknown(I[2])) |-> (O === I[2] && OB === ~I[2]) );
  assert property ( (S === 2'b11 && !$isunknown(I[3])) |-> (O === I[3] && OB === ~I[3]) );

  // Differential outputs must be complementary when driven (no X/Z)
  assert property ( (!$isunknown({O,OB})) |-> (OB == ~O) );

  // Coverage: hit each select value and both data polarities at the outputs
  cover property (S === 2'b00 && I[0] == 1'b0 && O == 1'b0 && OB == 1'b1);
  cover property (S === 2'b00 && I[0] == 1'b1 && O == 1'b1 && OB == 1'b0);

  cover property (S === 2'b01 && I[1] == 1'b0 && O == 1'b0 && OB == 1'b1);
  cover property (S === 2'b01 && I[1] == 1'b1 && O == 1'b1 && OB == 1'b0);

  cover property (S === 2'b10 && I[2] == 1'b0 && O == 1'b0 && OB == 1'b1);
  cover property (S === 2'b10 && I[2] == 1'b1 && O == 1'b1 && OB == 1'b0);

  cover property (S === 2'b11 && I[3] == 1'b0 && O == 1'b0 && OB == 1'b1);
  cover property (S === 2'b11 && I[3] == 1'b1 && O == 1'b1 && OB == 1'b0);
endmodule

// Bind into DUT
bind mux4_diff mux4_diff_sva u_mux4_diff_sva(.I(I), .S(S), .O(O), .OB(OB));