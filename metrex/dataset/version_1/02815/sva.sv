// SVA for bin_to_gray_converter
// Bindable, clockless, combinational-safe (uses @(*) and ##0 for settle)

module bin_to_gray_converter_sva (
  input logic [3:0] binary,
  input logic [3:0] gray
);

  // Functional equivalence (vector form)
  // gray == binary XOR (binary << 1) with LSB-anchored encoding
  assert property (@(*)
    !$isunknown(binary) |-> ##0
      (!$isunknown(gray) && gray == (binary ^ {binary[2:0],1'b0}))
  ) else $error("bin_to_gray: vector mismatch: bin=%0h gray=%0h exp=%0h",
                binary, gray, (binary ^ {binary[2:0],1'b0}));

  // Bit-accurate checks (aid debug)
  assert property (@(*) !$isunknown(binary[0]) |-> ##0 (gray[0] == binary[0]))
    else $error("bin_to_gray: g0!=b0 b0=%0b g0=%0b", binary[0], gray[0]);

  generate
    genvar i;
    for (i=1; i<4; i++) begin : G_BITMAP
      assert property (@(*)
        !$isunknown({binary[i],binary[i-1]}) |-> ##0
          (gray[i] == (binary[i] ^ binary[i-1]))
      ) else $error("bin_to_gray: g%0d!=b%0d^b%0d b=%0b g%0d=%0b",
                    i, i, i-1, binary, i, gray[i]);
    end
  endgenerate

  // Output stability when input stable; no spurious output changes
  assert property (@(*) $stable(binary) |-> ##0 $stable(gray))
    else $error("bin_to_gray: gray changed while binary stable");

  assert property (@(*) $changed(gray) |-> $changed(binary))
    else $error("bin_to_gray: gray changed without binary change");

  // Functional coverage: hit all 16 input codes and matching outputs
  generate
    genvar v;
    for (v=0; v<16; v++) begin : C_ALL_CODES
      localparam logic [3:0] V = v[3:0];
      cover property (@(*) (binary === V) ##0 (gray === (V ^ {V[2:0],1'b0})));
    end
  endgenerate

endmodule

// Bind into DUT
bind bin_to_gray_converter bin_to_gray_converter_sva sva_i (.binary(binary), .gray(gray));