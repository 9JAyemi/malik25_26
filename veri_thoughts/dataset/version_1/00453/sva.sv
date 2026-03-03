// SVA bind module for test
module test_sva(
  input logic a1, s1, s2, s3,
  input logic i1, i2, i3, i4, i5, i6, i7, i8
);

  // Functional equivalence (golden equations)
  always_comb begin
    assert (i1 === (a1 &  s1)) else $error("i1 mismatch");
    assert (i2 === (a1 &  s2)) else $error("i2 mismatch");
    assert (i3 === (a1 &  s3)) else $error("i3 mismatch");
    assert (i4 === (~a1 & s1)) else $error("i4 mismatch");
    assert (i5 === (~a1 & s2)) else $error("i5 mismatch");
    assert (i6 === (~a1 & s3)) else $error("i6 mismatch");
    assert (i7 === (s1 & s2 & s3)) else $error("i7 mismatch");
    assert (i8 === (~a1 & ~s1 & ~s2 & ~s3)) else $error("i8 mismatch");
  end

  // Pair coherence: for each sN, exactly one of the pair is 1 when sN==1, else both 0
  always_comb begin
    assert (s1 ? (i1 ^ i4) : !(i1 || i4)) else $error("s1/i1/i4 coherence");
    assert (s2 ? (i2 ^ i5) : !(i2 || i5)) else $error("s2/i2/i5 coherence");
    assert (s3 ? (i3 ^ i6) : !(i3 || i6)) else $error("s3/i3/i6 coherence");
  end

  // Global sanity
  always_comb begin
    assert (!(i7 && i8)) else $error("i7 and i8 cannot be 1 together");
  end

  // Optional X/Z check on outputs once inputs are known
  always_comb begin
    if (!$isunknown({a1,s1,s2,s3})) begin
      assert (!$isunknown({i1,i2,i3,i4,i5,i6,i7,i8})) else $error("X/Z on outputs");
    end
  end

  // Coverage: hit every output high, all-zeros case, and i7 with both a1 polarities
  always_comb begin
    cover (i1); cover (i2); cover (i3); cover (i4); cover (i5); cover (i6); cover (i7); cover (i8);
    cover (!i1 && !i2 && !i3 && !i4 && !i5 && !i6 && !i7 && !i8); // a1=1,s1=s2=s3=0
    cover (i7 &&  a1);
    cover (i7 && !a1);
  end

endmodule

// Bind into DUT
bind test test_sva u_test_sva (.*);