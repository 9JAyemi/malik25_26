// SVA checker for ACA_I_N16_Q4
// Binds to DUT and verifies functional mapping concisely.
// Uses immediate assertions (combinational), no clock required.

module ACA_I_N16_Q4_sva (
  input logic [15:0] in1,
  input logic [15:0] in2,
  input logic [16:0] res
);

  // Recompute expected result purely from ports (golden model)
  logic [4:0] s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13;
  logic [16:0] exp;

  always_comb begin
    s1  = in1[3:0]    + in2[3:0];
    s2  = in1[4:1]    + in2[4:1];
    s3  = in1[5:2]    + in2[5:2];
    s4  = in1[6:3]    + in2[6:3];
    s5  = in1[7:4]    + in2[7:4];
    s6  = in1[8:5]    + in2[8:5];
    s7  = in1[9:6]    + in2[9:6];
    s8  = in1[10:7]   + in2[10:7];
    s9  = in1[11:8]   + in2[11:8];
    s10 = in1[12:9]   + in2[12:9];
    s11 = in1[13:10]  + in2[13:10];
    s12 = in1[14:11]  + in2[14:11];
    s13 = in1[15:12]  + in2[15:12];

    exp = { s13[4:3], s12[3], s11[3], s10[3], s9[3], s8[3], s7[3], s6[3],
            s5[3], s4[3], s3[3], s2[3], s1[3:0] };
  end

  // Basic X/Z sanitation on ports
  always_comb begin
    assert (!$isunknown({in1, in2}))
      else $error("ACA_I_N16_Q4: X/Z on inputs in1=%h in2=%h", in1, in2);
    assert (!$isunknown(res))
      else $error("ACA_I_N16_Q4: X/Z on output res=%h", res);
  end

  // Core functional check (covers both the 4-bit slice adds and wiring)
  always_comb begin
    assert (res === exp)
      else $error("ACA_I_N16_Q4 mismatch: res=%h exp=%h in1=%h in2=%h", res, exp, in1, in2);
  end

  // Minimal but meaningful coverage
  always_comb begin
    // See at least one exact match sample
    cover (res === exp);
    // Exercise lower and upper edge conditions
    cover (s1  == 5'd0);        // low nibble zero-sum
    cover (s1[4]);              // low nibble carry
    cover (s13 == 5'd0);        // top nibble zero-sum
    cover (s13[4]);             // top nibble carry -> res[16]==1
    // Observe both LSB and MSB asserted at least once
    cover (res[0]);
    cover (res[16]);
    // Any mid-slice carry generated
    cover (s2[4] || s3[4] || s4[4] || s5[4] || s6[4] || s7[4] ||
           s8[4] || s9[4] || s10[4] || s11[4] || s12[4]);
  end

endmodule

// Bind into the DUT
bind ACA_I_N16_Q4 ACA_I_N16_Q4_sva u_ACA_I_N16_Q4_sva(.in1(in1), .in2(in2), .res(res));