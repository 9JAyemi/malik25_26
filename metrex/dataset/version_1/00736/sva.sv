// SVA for binary_to_gray
module binary_to_gray_sva(
  input [3:0] binary,
  input [3:0] gray
);

  // Functional mapping checks (guard against X on inputs/outputs)
  assert property (!$isunknown(binary) |-> (gray == {binary[2]^binary[3], binary[1]^binary[2], binary[0]^binary[1], binary[0]}));
  assert property (!$isunknown(gray)   |-> (binary == { (gray[3]^gray[2]^gray[1]^gray[0]),
                                                        (gray[2]^gray[1]^gray[0]),
                                                        (gray[1]^gray[0]),
                                                         gray[0]}));
  // Known inputs must produce known outputs
  assert property (!$isunknown(binary) |-> !$isunknown(gray));

  // Full functional input coverage (all 16 input combinations)
  cover property (binary == 4'h0);
  cover property (binary == 4'h1);
  cover property (binary == 4'h2);
  cover property (binary == 4'h3);
  cover property (binary == 4'h4);
  cover property (binary == 4'h5);
  cover property (binary == 4'h6);
  cover property (binary == 4'h7);
  cover property (binary == 4'h8);
  cover property (binary == 4'h9);
  cover property (binary == 4'hA);
  cover property (binary == 4'hB);
  cover property (binary == 4'hC);
  cover property (binary == 4'hD);
  cover property (binary == 4'hE);
  cover property (binary == 4'hF);

endmodule

bind binary_to_gray binary_to_gray_sva u_binary_to_gray_sva(.binary(binary), .gray(gray));