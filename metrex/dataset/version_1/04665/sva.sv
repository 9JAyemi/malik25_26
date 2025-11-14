// SVA for sparc_tlu_penc64: encodes index of the highest-set bit in `in`.
// Concise, complete checks + coverage.

bind sparc_tlu_penc64 sparc_tlu_penc64_sva i_sparc_tlu_penc64_sva (.in(in), .out(out));

module sparc_tlu_penc64_sva (
  input  logic [63:0] in,
  input  logic [5:0]  out
);

  // Helper: is there any bit set above idx?
  function automatic bit higher_set(input logic [63:0] v, input int idx);
    if (idx >= 63) higher_set = 1'b0;
    else           higher_set = |v[63:idx+1];
  endfunction

  default clocking cb @(*); endclocking

  // Correctness: if bit j is the MSB 1 (no higher ones), out must be j
  genvar j;
  generate
    for (j = 0; j < 64; j++) begin : g_msb_chk
      property p_msb_enc;
        in[j] && !higher_set(in, j) |-> (out == j[5:0]);
      endproperty
      a_msb_enc: assert property (p_msb_enc);

      // Coverage: see each MSB position encoded
      c_msb_enc: cover property (in[j] && !higher_set(in, j) && (out == j[5:0]));
    end
  endgenerate

  // All-zero input encodes to 0
  a_zero: assert property ( (in == 64'b0) |-> (out == 6'd0) );
  c_zero: cover  property ( (in == 64'b0) && (out == 6'd0) );

  // X-propagation sanity: known input implies known output
  a_known: assert property ( !$isunknown(in) |-> !$isunknown(out) );

endmodule