// SVA checker for binary_to_gray_converter
module binary_to_gray_converter_sva (
  input  logic [2:0] binary,
  input  logic [2:0] gray
);

  // Event to sample on any combinational change
  event comb_ev; always @* -> comb_ev;

  // Expected mapping
  let exp_gray = {binary[2], (binary[1]^binary[2]), (binary[0]^binary[1])};

  // Functional correctness (concurrent, sampled on any change)
  assert property (@comb_ev gray === exp_gray)
    else $error("Gray mapping mismatch: bin=%b gray=%b exp=%b", binary, gray, exp_gray);

  // Bitwise checks (redundant but pinpoint issues)
  assert property (@comb_ev gray[2] === binary[2])
    else $error("gray[2]!=binary[2]");
  assert property (@comb_ev gray[1] === (binary[1]^binary[2]))
    else $error("gray[1]!=b1^b2");
  assert property (@comb_ev gray[0] === (binary[0]^binary[1]))
    else $error("gray[0]!=b0^b1");

  // 4-state behavior: known input must yield fully known output; any X/Z in input must reflect in output
  assert property (@comb_ev (!$isunknown(binary)) |-> (!$isunknown(gray)))
    else $error("Output has X/Z while input is fully known");
  assert property (@comb_ev $isunknown(binary) |-> $isunknown(gray))
    else $error("X/Z in input did not propagate to output");

  // Coverage: hit all input/output pairs
  cover property (@comb_ev (binary==3'b000 && gray==3'b000));
  cover property (@comb_ev (binary==3'b001 && gray==3'b001));
  cover property (@comb_ev (binary==3'b010 && gray==3'b011));
  cover property (@comb_ev (binary==3'b011 && gray==3'b010));
  cover property (@comb_ev (binary==3'b100 && gray==3'b110));
  cover property (@comb_ev (binary==3'b101 && gray==3'b111));
  cover property (@comb_ev (binary==3'b110 && gray==3'b101));
  cover property (@comb_ev (binary==3'b111 && gray==3'b100));

  // Coverage: all Gray codes seen
  cover property (@comb_ev (gray inside {3'b000,3'b001,3'b011,3'b010,3'b110,3'b111,3'b101,3'b100}));

  // Coverage: X/Z propagation observed
  cover property (@comb_ev ($isunknown(binary) && $isunknown(gray)));

endmodule

// Bind into DUT
bind binary_to_gray_converter binary_to_gray_converter_sva sva_i(.binary(binary), .gray(gray));