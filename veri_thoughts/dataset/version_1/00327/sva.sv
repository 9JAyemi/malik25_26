// SystemVerilog Assertions for RCA_4bit and FA_1
// Focused, concise, full functional checks and coverage.
// Bind as shown at bottom.

module fa_1_sva (input A, input B, input Ci, input S, input Co);
  // Functional check
  always_comb begin
    if (!$isunknown({A,B,Ci,S,Co})) begin
      assert ({Co,S} === A + B + Ci)
        else $error("FA_1 mismatch: A=%0b B=%0b Ci=%0b => S=%0b Co=%0b", A,B,Ci,S,Co);
    end
  end

  // Simple endpoint coverage
  always_comb begin
    cover ({A,B,Ci} == 3'b000 && {Co,S} == 2'b00);
    cover ({A,B,Ci} == 3'b111 && {Co,S} == 2'b11);
  end
endmodule


module rca_4bit_sva (
  input  [3:0] A,
  input  [3:0] B,
  input        Ci,
  input  [3:0] S,
  input        Co,
  input  [3:1] CTMP
);
  // Local carry-in per stage
  wire [3:0] c_in;
  assign c_in[0] = Ci;
  assign c_in[1] = CTMP[1];
  assign c_in[2] = CTMP[2];
  assign c_in[3] = CTMP[3];

  // Top-level functional equivalence and X-prop
  always_comb begin
    if (!$isunknown({A,B,Ci})) begin
      assert (!$isunknown({S,Co}))
        else $error("RCA_4bit X/Z on outputs with known inputs");
      assert ({Co,S} === A + B + Ci)
        else $error("RCA_4bit sum mismatch: A=%0h B=%0h Ci=%0b => S=%0h Co=%0b", A,B,Ci,S,Co);
    end
  end

  // Per-bit sum checks
  genvar i;
  generate
    for (i = 0; i < 4; i++) begin: g_sum
      always_comb begin
        if (!$isunknown({A[i],B[i],c_in[i],S[i]})) begin
          assert (S[i] === (A[i] ^ B[i] ^ c_in[i]))
            else $error("Bit %0d sum mismatch", i);
        end
      end
    end
  endgenerate

  // Carry chain checks for internal CTMP[1..3]
  generate
    for (i = 0; i < 3; i++) begin: g_carry_mid
      wire expected_c = (A[i] & B[i]) | (A[i] & c_in[i]) | (B[i] & c_in[i]);
      always_comb begin
        if (!$isunknown({A[i],B[i],c_in[i],CTMP[i+1]})) begin
          assert (CTMP[i+1] === expected_c)
            else $error("CTMP[%0d] mismatch", i+1);
        end
      end
    end
  endgenerate

  // Final carry-out check
  always_comb begin
    if (!$isunknown({A[3],B[3],c_in[3],Co})) begin
      assert (Co === ((A[3] & B[3]) | (A[3] & c_in[3]) | (B[3] & c_in[3])))
        else $error("Final Co mismatch");
    end
  end

  // Full functional coverage of all 32 sum values
  generate
    genvar v;
    for (v = 0; v < 32; v++) begin: g_sumcov
      localparam logic [4:0] SUMVAL = v[4:0];
      always_comb cover ({Co,S} === SUMVAL);
    end
  endgenerate

  // Coverage: internal carries exercise 0 and 1
  genvar j;
  generate
    for (j = 1; j <= 3; j++) begin: g_ctmpcov
      always_comb begin
        cover (CTMP[j] == 1'b0);
        cover (CTMP[j] == 1'b1);
      end
    end
  endgenerate

  // Coverage: full carry propagate chain
  always_comb begin
    cover (((A ^ B) == 4'hF) && (Ci == 1'b0) && (Co == 1'b0));
    cover (((A ^ B) == 4'hF) && (Ci == 1'b1) && (Co == 1'b1));
  end
endmodule


// Bind the SVA modules to the DUTs
bind FA_1    fa_1_sva     u_fa_1_sva (.*);
bind RCA_4bit rca_4bit_sva u_rca_4bit_sva (.A(A), .B(B), .Ci(Ci), .S(S), .Co(Co), .CTMP(CTMP));