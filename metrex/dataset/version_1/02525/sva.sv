// SVA checker for booth_encoder_5
module booth_encoder_5_sva (
  input logic [2:0] B_in,
  input logic [2:0] A_out
);

  // Golden model (truth table reduced from priority chain)
  function automatic logic [2:0] exp (input logic [2:0] b);
    unique case (b)
      3'b000:                         exp = 3'b000;
      3'b001,3'b010,3'b100,3'b111:    exp = 3'b001;
      3'b011,3'b110:                  exp = 3'b010;
      3'b101:                         exp = 3'b011;
      default:                        exp = 3'bxxx; // any X/Z in input -> don't-care
    endcase
  endfunction

  // Combinational correctness, range, and knownness
  always_comb begin
    assert (#0 (A_out === exp(B_in)))
      else $error("booth_encoder_5 mismatch B_in=%b A_out=%b exp=%b", B_in, A_out, exp(B_in));
    assert (#0 (A_out inside {3'b000,3'b001,3'b010,3'b011}))
      else $error("booth_encoder_5 illegal code A_out=%b for B_in=%b", A_out, B_in);
    if (!$isunknown(B_in)) assert (#0 !$isunknown(A_out))
      else $error("booth_encoder_5 X/Z on A_out with known B_in: B_in=%b A_out=%b", B_in, A_out);
  end

  // Functional coverage (hit every input/output bucket)
  always_comb begin
    cover (B_in==3'b000 && A_out==3'b000);
    cover (B_in inside {3'b001,3'b010,3'b100,3'b111} && A_out==3'b001);
    cover (B_in inside {3'b011,3'b110} && A_out==3'b010);
    cover (B_in==3'b101 && A_out==3'b011);
  end

endmodule

// Bind into DUT
bind booth_encoder_5 booth_encoder_5_sva u_booth_encoder_5_sva (.B_in(B_in), .A_out(A_out));