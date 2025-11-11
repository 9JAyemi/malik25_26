// SVA for top_module and barrel_shifter
// Bind these into your simulation/formal environment

// Top-level assertions and coverage
module top_module_sva (
  input  logic [15:0] A,
  input  logic [15:0] B,                  // unused by top_module, kept for uniform bind (ignored)
  input  logic [3:0]  S,
  input  logic [3:0]  input_bcd,
  input  logic [15:0] barrel_shifter_output,
  input  logic [7:0]  bcd_converter_output,
  input  logic [7:0]  final_output
);
  always_comb begin
    automatic logic inputs_known = !$isunknown({A,S,input_bcd});
    automatic logic [15:0] expected_shift = (inputs_known) ? (A << S) : 'x;
    automatic logic [7:0]  expected_bcd  = (inputs_known) ? ((input_bcd==4'hF) ? 8'h00 : {4'b0000,input_bcd}) : 'x;
    automatic logic [8:0]  sum9          = {1'b0, expected_shift[15:8]} + {1'b0, expected_bcd};

    if (inputs_known) begin
      // Barrel shifter check
      assert (barrel_shifter_output == expected_shift)
        else $error("barrel_shifter_output mismatch: A=%h S=%0d got=%h exp=%h",
                    A,S,barrel_shifter_output, expected_shift);

      if (S!=0) assert (barrel_shifter_output[S-1:0] == '0)
        else $error("Low bits after shift not zero: S=%0d out=%h", S, barrel_shifter_output);

      // BCD converter check (0..14 pass-through, 15 -> 0)
      assert (bcd_converter_output == expected_bcd)
        else $error("bcd_converter_output mismatch: input_bcd=%0d got=%h exp=%h",
                    input_bcd, bcd_converter_output, expected_bcd);

      assert (bcd_converter_output[7:4] == 4'h0)
        else $error("bcd_converter_output upper nibble nonzero: %h", bcd_converter_output);

      // Final output check (8-bit truncation)
      assert (final_output == sum9[7:0])
        else $error("final_output mismatch: upper(A<<S)=%h bcd=%h got=%h exp=%h",
                    expected_shift[15:8], expected_bcd, final_output, sum9[7:0]);

      // No X/Z on outputs when inputs are known
      assert (!$isunknown({barrel_shifter_output,bcd_converter_output,final_output}))
        else $error("Unknown detected on outputs");
    end

    // Minimal functional coverage
    cover (S == 4'd0);
    cover (S == 4'd15);
    cover (A == 16'h0000);
    cover (A == 16'h0001);
    cover (A[15]);                 // MSB set in A
    cover (input_bcd == 4'h0);
    cover (input_bcd == 4'h9);
    cover (input_bcd == 4'hA);
    cover (input_bcd == 4'hE);
    cover (input_bcd == 4'hF);     // special case -> 0
    cover (sum9[8]);               // addition overflow (carry-out)
    cover (final_output == 8'h00);
    cover (final_output == 8'hFF);
  end

  // Exhaustive coverage for all S values
  genvar gs;
  generate
    for (gs=0; gs<16; gs++) begin: g_s_cov
      always_comb cover (S == gs[3:0]);
    end
  endgenerate

  // Exhaustive coverage for all BCD input values
  genvar gb;
  generate
    for (gb=0; gb<16; gb++) begin: g_bcd_cov
      always_comb cover (input_bcd == gb[3:0]);
    end
  endgenerate

  // Cover shifted upper byte being zero/non-zero
  always_comb begin
    automatic logic [15:0] sh = A << S;
    cover (sh[15:8] == 8'h00);
    cover (sh[15:8] != 8'h00);
  end
endmodule

// Assertions and coverage for the standalone barrel_shifter module
module barrel_shifter_sva (
  input  logic [15:0] A,
  input  logic [15:0] B,     // should not affect Y
  input  logic [3:0]  S,
  input  logic [15:0] Y
);
  always_comb begin
    if (!$isunknown({A,S})) begin
      automatic logic [15:0] exp = A << S;
      assert (Y == exp)
        else $error("barrel_shifter.Y mismatch: A=%h S=%0d got=%h exp=%h", A,S,Y,exp);
      if (S!=0) assert (Y[S-1:0] == '0)
        else $error("barrel_shifter low bits not zero: S=%0d Y=%h", S, Y);
      // No X/Z when inputs known
      assert (!$isunknown(Y)) else $error("barrel_shifter Y unknown");
    end
    // Independence from B is implied by functional check above
  end

  // Exhaustive S coverage
  genvar gs2;
  generate
    for (gs2=0; gs2<16; gs2++) begin: g_s_cov2
      always_comb cover (S == gs2[3:0]);
    end
  endgenerate

  // Corner coverage
  always_comb begin
    cover (A == 16'h0000);
    cover (A == 16'h8000);
    cover (S == 4'd0);
    cover (S == 4'd15);
  end
endmodule

// Bind directives
bind top_module      top_module_sva      top_sva_i (
  .A(A),
  .B(16'h0),
  .S(S),
  .input_bcd(input_bcd),
  .barrel_shifter_output(barrel_shifter_output),
  .bcd_converter_output(bcd_converter_output),
  .final_output(final_output)
);

bind barrel_shifter  barrel_shifter_sva  bsh_sva_i (
  .A(A),
  .B(B),
  .S(S),
  .Y(Y)
);