// Bindable SVA for four_bit_subtractor and one_bit_subtractor
// Focused, concise, and high-value checks + coverage

// Checker for the leaf one_bit_subtractor
module one_bit_subtractor_sva(
  input logic A, B, Bin,
  input logic Diff, BorrowOut
);
  // Functional spec
  always_comb begin
    assert (Diff      == (A ^ B ^ Bin))
      else $error("1b Diff mismatch: A=%0b B=%0b Bin=%0b Diff=%0b", A,B,Bin,Diff);
    assert (BorrowOut == ((~A & B) | (~A & Bin) | (B & Bin)))
      else $error("1b BorrowOut mismatch: A=%0b B=%0b Bin=%0b BorrowOut=%0b", A,B,Bin,BorrowOut);
  end

  // No X/Z leakage when inputs are clean
  always_comb if (!$isunknown({A,B,Bin}))
    assert (!$isunknown({Diff,BorrowOut}))
      else $error("1b outputs X/Z with clean inputs");

  // Simple functional coverage
  cover property (@(A or B or Bin) (Bin==0) && (A^B));        // no-borrow-in, toggle case
  cover property (@(A or B or Bin) (Bin==1) && (A==0) && B);  // classic borrow creation
endmodule

// Checker for four_bit_subtractor, bound to internal nets
module four_bit_subtractor_sva(
  input  logic [3:0] A, B, C,
  input  logic       Borrow,
  input  logic [3:0] diff,
  input  logic       borrow1, borrow2
);
  // Golden unsigned-subtraction spec
  logic [4:0] gold;
  always_comb begin
    gold = {1'b0,A} - {1'b0,B};
    assert (C == gold[3:0])
      else $error("C mismatch: A=%0h B=%0h C=%0h gold=%0h", A,B,C,gold[3:0]);
    assert (Borrow == (A < B))
      else $error("Borrow mismatch: A=%0h B=%0h Borrow=%0b gold=%0b", A,B,Borrow,(A<B));
  end

  // Ripple path checks and internal net consistency
  always_comb begin
    // stage 0
    assert (diff[0] == (A[0] ^ B[0])) else $error("diff[0] mismatch");
    assert (borrow1 == (~A[0] & B[0])) else $error("borrow1 mismatch");
    // stage 1
    assert (diff[1] == (A[1] ^ B[1] ^ borrow1)) else $error("diff[1] mismatch");
    assert (borrow2 == ((~A[1] & B[1]) | (~A[1] & borrow1) | (B[1] & borrow1)))
      else $error("borrow2 mismatch");
    // stage 2 (Borrow here is borrow out of bit[2] in DUT)
    assert (diff[2] == (A[2] ^ B[2] ^ borrow2)) else $error("diff[2] mismatch");
    assert (Borrow  == ((~A[2] & B[2]) | (~A[2] & borrow2) | (B[2] & borrow2)))
      else $error("Borrow (bit2 out) mismatch");
    // MSB diff and final output mapping
    assert (diff[3] == (A[3] ^ B[3] ^ Borrow)) else $error("diff[3] mismatch");
    assert (C == diff) else $error("C != diff bus");
  end

  // No X/Z leakage when inputs are clean
  always_comb if (!$isunknown({A,B}))
    assert (!$isunknown({C,Borrow,diff,borrow1,borrow2}))
      else $error("Outputs/internal X/Z with clean inputs");

  // High-value coverage
  cover property (@(A or B) (A==B));          // zero result, no borrow
  cover property (@(A or B) (A<B));           // wraparound with borrow
  cover property (@(A or B) (A>B));           // normal subtract
  cover property (@(A or B) (A==4'h0 && B==4'hF)); // worst-case borrow
  cover property (@(A or B) (A==4'hF && B==4'h0)); // no borrow, all-ones result
  cover property (@(A or B) (!borrow1 && !borrow2 && !Borrow)); // clean ripple
  cover property (@(A or B) (borrow1 && borrow2 && Borrow));     // deep borrow chain
endmodule

// Bind into DUTs (connects to internal nets in four_bit_subtractor)
bind one_bit_subtractor   one_bit_subtractor_sva   u_obs_sva(.*);
bind four_bit_subtractor  four_bit_subtractor_sva  u_4bsub_sva(
  .A(A), .B(B), .C(C), .Borrow(Borrow),
  .diff(diff), .borrow1(borrow1), .borrow2(borrow2)
);