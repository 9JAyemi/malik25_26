// SVA checker for priority_encoder (4→16 one-hot decoder)
// Concise, high-quality properties; combinational sampling via @(*)

module priority_encoder_sva (
  input logic [3:0]  I,
  input logic [15:0] O
);
  default clocking cb @(*); endclocking

  // Functional equivalence: for known I, O must be exactly (1 << I)
  assert property ( !$isunknown(I) |-> (O == (16'h1 << I)) )
    else $error("Decode mismatch: I=%0h O=%0h", I, O);

  // One-hot and known O when I is known
  assert property ( !$isunknown(I) |-> ($onehot(O) && !$isunknown(O)) )
    else $error("O not one-hot/known for known I=%0h (O=%0h)", I, O);

  // Bidirectional bitwise checks + per-value coverage
  genvar k;
  generate
    for (k = 0; k < 16; k++) begin : GEN_DEC_CHK
      // If I==k (and known), corresponding O[k] must be 1
      assert property ( (!$isunknown(I) && (I == k)) |-> O[k] )
        else $error("O[%0d] not set for I=%0d", k, k);

      // If O[k] is 1 with known I, I must equal k (no aliasing)
      assert property ( (O[k] && !$isunknown(I)) |-> (I == k) )
        else $error("O[%0d]=1 but I=%0d", k, I);

      // Coverage: observe each decoded value at least once
      cover property ( (I == k) && O[k] );
    end
  endgenerate
endmodule

// Bind into DUT
bind priority_encoder priority_encoder_sva sva(.I(I), .O(O));