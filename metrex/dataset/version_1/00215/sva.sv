// SVA for sevensegdecoder
// Concise, full functional checking and coverage via bind

module sevensegdecoder_sva (
  input  logic [4:0] nIn,
  input  logic [6:0] ssOut
);

  // Golden decode function
  function automatic logic [6:0] exp(input logic [4:0] v);
    case (v)
      5'h0:  exp = 7'b1000000;
      5'h1:  exp = 7'b1111001;
      5'h2:  exp = 7'b0100100;
      5'h3:  exp = 7'b0110000;
      5'h4:  exp = 7'b0011001;
      5'h5:  exp = 7'b0010010;
      5'h6:  exp = 7'b0000010;
      5'h7:  exp = 7'b1111000;
      5'h8:  exp = 7'b0000000;
      5'h9:  exp = 7'b0011000;
      5'hA:  exp = 7'b0001000;
      5'hB:  exp = 7'b0000011;
      5'hC:  exp = 7'b1000110;
      5'hD:  exp = 7'b0100001;
      5'hE:  exp = 7'b0000110;
      5'hF:  exp = 7'b0001110;
      5'h10: exp = 7'b0101111;
      5'h11: exp = 7'b0001100;
      5'h12: exp = 7'b0000110;
      5'h13: exp = 7'b1111111;
      default: exp = 7'b1001001;
    endcase
  endfunction

  // Core functional equivalence: sample after combinational update (##0)
  a_decode: assert property (@(nIn) ##0 (ssOut === exp(nIn)))
    else $error("sevensegdecoder mismatch: nIn=%0h ssOut=%0b exp=%0b", nIn, ssOut, exp(nIn));

  // Sanity: outputs never X/Z
  a_no_x: assert property (@(nIn or ssOut) ##0 (!$isunknown(ssOut)))
    else $error("sevensegdecoder produced X/Z on ssOut: %0b for nIn=%0h", ssOut, nIn);

  // Functional coverage: all mapped inputs plus default bucket
  // General hit on any valid mapping
  c_any: cover property (@(nIn) ##0 (ssOut === exp(nIn)));

  // Per-code coverage for 0..0x13 using exp()
  genvar i;
  generate
    for (i = 0; i <= 5'h13; i++) begin : gen_cov
      c_code: cover property (@(nIn) ##0 (nIn == i[4:0] && ssOut == exp(i[4:0])));
    end
  endgenerate

  // Default bucket coverage (inputs 0x14..0x1F)
  c_default: cover property (@(nIn) ##0 ((nIn inside {[5'h14:5'h1F]}) && ssOut == 7'b1001001));

endmodule

// Bind into DUT
bind sevensegdecoder sevensegdecoder_sva sva_inst(.nIn(nIn), .ssOut(ssOut));