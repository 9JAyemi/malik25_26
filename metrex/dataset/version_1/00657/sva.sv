// SVA checker for SEG_HEX — concise, high-quality functional and safety checks with coverage
// Bind this to the DUT instance (no clock required; handles delta-cycle NBAs with ##0)

module SEG_HEX_sva (
  input logic [3:0] iDIG,
  input logic [6:0] oHEX_D
);

  // Golden mapping function
  function automatic logic [6:0] exp(input logic [3:0] d);
    case (d)
      4'h0: exp = 7'b1000000; 4'h1: exp = 7'b1111001; 4'h2: exp = 7'b0100100; 4'h3: exp = 7'b0110000;
      4'h4: exp = 7'b0011001; 4'h5: exp = 7'b0010010; 4'h6: exp = 7'b0000010; 4'h7: exp = 7'b1111000;
      4'h8: exp = 7'b0000000; 4'h9: exp = 7'b0011000; 4'ha: exp = 7'b0001000; 4'hb: exp = 7'b0000011;
      4'hc: exp = 7'b1000110; 4'hd: exp = 7'b0100001; 4'he: exp = 7'b0000110; 4'hf: exp = 7'b0001110;
    endcase
  endfunction

  // 1) No X/Z on inputs or outputs (sample after NBA)
  property p_no_xz;
    @(iDIG or oHEX_D) ##0 (!$isunknown(iDIG) && !$isunknown(oHEX_D));
  endproperty
  assert property (p_no_xz)
    else $error("SEG_HEX: X/Z detected on iDIG or oHEX_D");

  // 2) Functional equivalence: output must match golden mapping (sample after NBA)
  property p_func;
    @(iDIG or oHEX_D) ##0 (oHEX_D == exp(iDIG));
  endproperty
  assert property (p_func)
    else $error("SEG_HEX: oHEX_D != expected(iDIG)  iDIG=%h oHEX_D=%b exp=%b", iDIG, oHEX_D, exp(iDIG));

  // 3) Output must always be one of the 16 legal 7-seg patterns (safety net)
  property p_legal_pattern;
    @(oHEX_D) ##0 (oHEX_D inside {
      7'b1000000, 7'b1111001, 7'b0100100, 7'b0110000,
      7'b0011001, 7'b0010010, 7'b0000010, 7'b1111000,
      7'b0000000, 7'b0011000, 7'b0001000, 7'b0000011,
      7'b1000110, 7'b0100001, 7'b0000110, 7'b0001110
    });
  endproperty
  assert property (p_legal_pattern)
    else $error("SEG_HEX: Illegal 7-seg pattern on oHEX_D=%b", oHEX_D);

  // Coverage
  // 4) Cover the functional relation firing (overall mapping exercised)
  cover property (p_func);

  // 5) Cover each input nibble seen at least once
  genvar gi;
  generate
    for (gi = 0; gi < 16; gi++) begin : COV_IN
      cover property (@(iDIG) (iDIG == gi[3:0]));
    end
  endgenerate

  // 6) Cover each legal output pattern observed at least once
  //    (mirrors the 16 encodings)
  localparam logic [6:0] LEGAL [0:15] = '{
    7'b1000000, 7'b1111001, 7'b0100100, 7'b0110000,
    7'b0011001, 7'b0010010, 7'b0000010, 7'b1111000,
    7'b0000000, 7'b0011000, 7'b0001000, 7'b0000011,
    7'b1000110, 7'b0100001, 7'b0000110, 7'b0001110
  };
  genvar go;
  generate
    for (go = 0; go < 16; go++) begin : COV_OUT
      cover property (@(oHEX_D) (oHEX_D == LEGAL[go]));
    end
  endgenerate

endmodule

// Bind into all instances of SEG_HEX
bind SEG_HEX SEG_HEX_sva u_SEG_HEX_sva (.iDIG(iDIG), .oHEX_D(oHEX_D));