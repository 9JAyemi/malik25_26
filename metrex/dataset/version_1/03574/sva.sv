// SVA checker and bind for four_bit_complement
checker four_bit_complement_chk (input logic [3:0] A,
                                 input logic       S,
                                 input logic [3:0] Y);

  // Combinational, race-free sampling
  always_comb begin
    automatic logic [3:0] exp = (~A) + {3'b0, ~S};  // exp = ~A (+1 when S==0)

    if (!$isunknown({A,S})) begin
      assert (#0 !$isunknown(Y)) else $error("Y has X/Z with known inputs");
      assert (#0 (Y == exp))     else $error("Functional mismatch: Y=%0h exp=%0h A=%0h S=%0b", Y, exp, A, S);

      // Algebraic sanity: Y+A = 0x0 when S==0 (two's comp), 0xF when S==1 (one's comp)
      assert (#0 ((Y + A) == (S ? 4'hF : 4'h0)))
        else $error("Sum check failed: Y+A=%0h A=%0h S=%0b", (Y+A), A, S);
    end

    // Lightweight coverage
    cover (!$isunknown({A,S})) && (S==0);
    cover (!$isunknown({A,S})) && (S==1);
    cover (!$isunknown({A,S,Y}) && S==0 && A==4'h0 && Y==4'h0); // 2's comp zero
    cover (!$isunknown({A,S,Y}) && S==0 && A==4'hF && Y==4'h1); // wrap + carry drop
    cover (!$isunknown({A,S,Y}) && S==1 && A==4'h0 && Y==4'hF); // 1's comp zero
    cover (!$isunknown({A,S,Y}) && S==1 && A==4'hF && Y==4'h0); // 1's comp all-ones
  end
endchecker

bind four_bit_complement four_bit_complement_chk u_four_bit_complement_chk (.A(A), .S(S), .Y(Y));