// SVA checker for four_to_sixteen_decoder
// Notes:
// - Checks exact decode mapping into lower nibble
// - Ensures upper 12 bits are 0 and one-hot behavior
// - X/Z handling on sel produces 0
// - Provides compact functional coverage

module four_to_sixteen_decoder_sva
  (
    input  logic [1:0]  sel,
    input  logic [15:0] out
  );

  // Trigger assertions/coverage whenever sel or out changes
  event comb_ev;
  always @(sel or out) -> comb_ev;

  // Known select must decode to 1<<sel in lower nibble (and by equality, zeros elsewhere)
  property p_decode_known;
    !$isunknown(sel) |-> (out == (16'h1 << sel));
  endproperty
  assert property (@(comb_ev) p_decode_known)
    else $error("Decode mismatch: sel=%b out=%h", sel, out);

  // Unknown select must drive 0 (per default case)
  property p_decode_unknown_is_zero;
    $isunknown(sel) |-> (out == 16'h0000);
  endproperty
  assert property (@(comb_ev) p_decode_unknown_is_zero)
    else $error("Unknown sel must produce 0: sel=%b out=%h", sel, out);

  // Structural form: exactly one bit set in out[3:0], upper bits zero (redundant but tight)
  property p_onehot_lower_upper_zero;
    (out[15:4] == 12'h000) && $onehot(out[3:0]);
  endproperty
  assert property (@(comb_ev) p_onehot_lower_upper_zero)
    else $error("Output must be one-hot in lower nibble and zero elsewhere: out=%h", out);

  // No X/Z on out when sel is known
  property p_no_x_out_when_sel_known;
    !$isunknown(sel) |-> !$isunknown(out);
  endproperty
  assert property (@(comb_ev) p_no_x_out_when_sel_known)
    else $error("Out has X/Z while sel is known: sel=%b out=%h", sel, out);

  // Output must be one of the 5 legal values (covers both known and unknown sel cases)
  property p_legal_values;
    out inside {16'h0000,16'h0001,16'h0002,16'h0004,16'h0008};
  endproperty
  assert property (@(comb_ev) p_legal_values)
    else $error("Illegal out value: %h", out);

  // Functional coverage: hit all four decodes
  genvar i;
  generate
    for (i = 0; i < 4; i++) begin : COV
      cover property (@(comb_ev) (! $isunknown(sel)) && (sel == i[1:0]) && (out == (16'h1 << i)));
    end
  endgenerate

  // Optional: cover unknown sel case producing zero
  cover property (@(comb_ev) $isunknown(sel) && (out == 16'h0000));

endmodule

// Bind into DUT
bind four_to_sixteen_decoder four_to_sixteen_decoder_sva u_four_to_sixteen_decoder_sva (
  .sel(sel),
  .out(out)
);