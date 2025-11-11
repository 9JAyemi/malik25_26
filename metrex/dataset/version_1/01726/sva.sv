// SVA for binary_adder and full_adder
// Concise, high-quality checks + meaningful coverage. No clock required.

// Bind into binary_adder: check math, chain equations, connectivity, X-handling, coverage.
module binary_adder_sva;
  // Structural connectivity checks (4-state to allow X tracking)
  always_comb begin
    assert (fa0.Cin  == 1'b0)      else $error("fa0.Cin != 0");
    assert (fa0.S    === sum[0])   else $error("fa0.S != sum[0]");
    assert (fa0.Cout === carry[0]) else $error("fa0.Cout != carry[0]");

    assert (fa1.Cin  === carry[0]) else $error("fa1.Cin != carry[0]");
    assert (fa1.S    === sum[1])   else $error("fa1.S != sum[1]");
    assert (fa1.Cout === carry[1]) else $error("fa1.Cout != carry[1]");

    assert (fa2.Cin  === carry[1]) else $error("fa2.Cin != carry[1]");
    assert (fa2.S    === sum[2])   else $error("fa2.S != sum[2]");
    assert (fa2.Cout === carry[2]) else $error("fa2.Cout != carry[2]");

    assert (fa3.Cin  === carry[2]) else $error("fa3.Cin != carry[2]");
    assert (fa3.S    === sum[3])   else $error("fa3.S != sum[3]");
    assert (fa3.Cout === Cout)     else $error("fa3.Cout != Cout");

    // Output aliasing
    assert (S === sum) else $error("S is not equal to internal sum");
  end

  // Functional correctness and X-handling
  always_comb begin
    if (!$isunknown({A,B})) begin
      assert (!$isunknown({S,Cout})) else $error("Outputs X/Z with known inputs");

      // Full-width correctness: {Cout,S} equals zero-extended A+B
      assert ({Cout,S} == ({1'b0,A} + {1'b0,B}))
        else $error("Adder result mismatch: {Cout,S} != A+B");

      // Bit-slice equations
      assert (sum[0]   == (A[0] ^ B[0]))      else $error("sum[0] wrong");
      assert (carry[0] == (A[0] & B[0]))      else $error("carry[0] wrong");

      for (int i=1; i<4; i++) begin
        assert (sum[i]   == ((A[i]^B[i]) ^ carry[i-1]))
          else $error("sum[%0d] wrong", i);
        assert (carry[i] == ((A[i]&B[i]) | ((A[i]^B[i]) & carry[i-1])))
          else $error("carry[%0d] wrong", i);
      end

      assert (Cout == ((A[3]&B[3]) | ((A[3]^B[3]) & carry[2])))
        else $error("Cout wrong");
    end
  end

  // Lightweight but meaningful coverage
  always_comb begin
    // Corner sums
    cover ({Cout,S} == 5'd0);                 // 0+0
    cover (A==4'd0  && B==4'd15);             // max on B
    cover (A==4'd15 && B==4'd0);              // max on A
    cover (A==4'd15 && B==4'd15 && Cout);     // overflow

    // Generate/propagate/kill seen on each bit
    for (int i=0;i<4;i++) begin
      cover (A[i] & B[i]);        // generate
      cover (A[i] ^ B[i]);        // propagate
      cover (!(A[i] | B[i]));     // kill
    end

    // Full ripple through bits 1..3 from bit0 generate
    cover ((A[0]&B[0]) && (A[1]^B[1]) && (A[2]^B[2]) && (A[3]^B[3]) && Cout);
  end
endmodule

bind binary_adder binary_adder_sva ba_sva();

// Bind into full_adder: gate-level relations, functional form, X-handling, coverage.
module full_adder_sva;
  always_comb begin
    // Structural gate relations (4-state)
    assert (xor1 === (A ^ B))         else $error("xor1 mismatch");
    assert (and1 === (A & B))         else $error("and1 mismatch");
    assert (and2 === (xor1 & Cin))    else $error("and2 mismatch");
    assert (S    === (xor1 ^ Cin))    else $error("S mismatch vs xor1^Cin");
    assert (Cout === (and1 | and2))   else $error("Cout mismatch vs or(and1,and2)");

    // Functional when inputs known
    if (!$isunknown({A,B,Cin})) begin
      assert (!$isunknown({S,Cout})) else $error("FA outputs X/Z with known inputs");
      assert (S    == (A ^ B ^ Cin)) else $error("FA S wrong");
      assert (Cout == ((A & B) | ((A ^ B) & Cin)))
        else $error("FA Cout wrong");
    end

    // Coverage: kill/propagate/generate and carry behavior
    cover (!A && !B && !Cin);                 // kill, zero result
    cover ((A ^ B) && Cin && Cout);           // propagate with carry-in causes carry-out
    cover ((A & B) && !Cin && Cout);          // generate without carry-in
    cover (S && !Cout);                       // sum=1, no carry-out
    cover (!S && Cout);                       // carry-out with even parity
  end
endmodule

bind full_adder full_adder_sva fa_sva();