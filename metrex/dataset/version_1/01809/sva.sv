// SVA checker for binary_to_gray
module binary_to_gray_sva(input logic [2:0] bin, input logic [2:0] gray);

  // No X/Z on inputs/outputs
  always_comb begin
    assert (!$isunknown(bin))  else $error("binary_to_gray: bin has X/Z: %b", bin);
    assert (!$isunknown(gray)) else $error("binary_to_gray: gray has X/Z: %b", gray);
  end

  // Functional correctness: 3-bit binary -> Gray code
  always_comb begin
    assert (gray == {bin[2], bin[2]^bin[1], bin[1]^bin[0]})
      else $error("binary_to_gray mismatch: bin=%0b gray=%0b exp=%0b",
                  bin, gray, {bin[2], bin[2]^bin[1], bin[1]^bin[0]});
  end

  // Full functional coverage of all input/output pairs
  always_comb begin
    cover (bin == 3'b000 && gray == 3'b000);
    cover (bin == 3'b001 && gray == 3'b001);
    cover (bin == 3'b010 && gray == 3'b011);
    cover (bin == 3'b011 && gray == 3'b010);
    cover (bin == 3'b100 && gray == 3'b110);
    cover (bin == 3'b101 && gray == 3'b111);
    cover (bin == 3'b110 && gray == 3'b101);
    cover (bin == 3'b111 && gray == 3'b100);
  end

  // Compact bit toggle coverage
  always_comb begin
    cover (gray[0]); cover (!gray[0]);
    cover (gray[1]); cover (!gray[1]);
    cover (gray[2]); cover (!gray[2]);
  end

endmodule

// Bind the checker to all instances of the DUT
bind binary_to_gray binary_to_gray_sva u_binary_to_gray_sva (.bin(bin), .gray(gray));