// SVA checker + bind for binary_to_one_hot
module binary_to_one_hot_sva (
  input logic [3:0] B,
  input logic       O0, O1, O2, O3
);
  logic [3:0] O;
  assign O = {O3,O2,O1,O0};

  // Core functional check + sanity
  always_comb begin
    assert #0 (O == ($onehot(B) ? B : 4'b0000))
      else $error("binary_to_one_hot: wrong decode B=%b O=%b", B, O);

    assert #0 ($onehot0(O))
      else $error("binary_to_one_hot: outputs not onehot0 O=%b", O);

    if (O0) assert #0 (B == 4'b0001) else $error("O0 high but B!=0001: B=%b", B);
    if (O1) assert #0 (B == 4'b0010) else $error("O1 high but B!=0010: B=%b", B);
    if (O2) assert #0 (B == 4'b0100) else $error("O2 high but B!=0100: B=%b", B);
    if (O3) assert #0 (B == 4'b1000) else $error("O3 high but B!=1000: B=%b", B);

    if (!$isunknown(B)) assert #0 (!$isunknown(O))
      else $error("Outputs have X/Z for known B: B=%b O=%b", B, O);
  end

  // Coverage (valid cases + default)
  always_comb begin
    cover #0 (B==4'b0001 && O==4'b0001);
    cover #0 (B==4'b0010 && O==4'b0010);
    cover #0 (B==4'b0100 && O==4'b0100);
    cover #0 (B==4'b1000 && O==4'b1000);
    cover #0 (B==4'b0000 && O==4'b0000);          // explicit default-idle
    cover #0 (!$onehot(B) && B!=4'b0000 && O==4'b0000); // any other invalid input
  end
endmodule

bind binary_to_one_hot binary_to_one_hot_sva u_binary_to_one_hot_sva (
  .B(B), .O0(O0), .O1(O1), .O2(O2), .O3(O3)
);