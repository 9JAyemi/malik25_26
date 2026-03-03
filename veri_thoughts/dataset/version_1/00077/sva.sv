// SVA checker + bind for binary_to_onehot

checker binary_to_onehot_sva (input logic [3:0] B, input logic [7:0] O);

  function automatic logic [7:0] expected (input logic [3:0] b);
    unique case (b)
      4'b0001: expected = 8'b00000001;
      4'b0010: expected = 8'b00000010;
      4'b0100: expected = 8'b00000100;
      4'b1000: expected = 8'b00001000;
      default: expected = 8'b00000000;
    endcase
  endfunction

  // Functional equivalence and structural invariants (combinational block)
  always_comb begin
    assert (O === expected(B))
      else $error("binary_to_onehot mismatch: B=%b O=%b exp=%b", B, O, expected(B));

    assert (O[7:4] == 4'b0)
      else $error("Upper nibble of O must be 0, got %b (B=%b)", O[7:4], B);

    assert ($onehot0(O[3:0]))
      else $error("Lower nibble of O must be onehot or zero, got %b (B=%b)", O[3:0], B);

    // X/Z on B must drive O==0 per case default
    if ($isunknown(B))
      assert (O === 8'b0)
        else $error("With X/Z on B, O must be 0, got %b (B=%b)", O, B);
  end

  // Coverage: each decode, explicit default zero, illegal inputs, and X/Z handling
  always_comb begin
    cover (B == 4'b0001 && O == 8'b00000001);
    cover (B == 4'b0010 && O == 8'b00000010);
    cover (B == 4'b0100 && O == 8'b00000100);
    cover (B == 4'b1000 && O == 8'b00001000);
    cover ((B == 4'b0000) && (O == 8'b00000000));
    cover (($countones(B) >= 2) && (O == 8'b00000000));
    cover ($isunknown(B) && (O === 8'b00000000));
  end

endchecker

bind binary_to_onehot binary_to_onehot_sva chk (.B(B), .O(O));