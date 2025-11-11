// SVA for compute_tm_count (bindable, concise, full functional check + coverage)
module compute_tm_count_sva (
  input  logic        atm_valid,
  input  logic        dtm_valid,
  input  logic        itm_valid,
  input  logic [1:0]  compute_tm_count
);

  // Functional correctness for all known inputs (combinational, same tick)
  always_comb begin
    if (!$isunknown({itm_valid, atm_valid, dtm_valid})) begin
      logic [1:0] expected = itm_valid + atm_valid + dtm_valid;
      assert (compute_tm_count == expected)
        else $error("compute_tm_count mismatch: IAT=%b expected=%0d got=%0d",
                    {itm_valid, atm_valid, dtm_valid}, expected, compute_tm_count);
      assert (!$isunknown(compute_tm_count))
        else $error("compute_tm_count is X/Z with known inputs");
    end
  end

  // Sanity: legal range when known
  always_comb begin
    if (!$isunknown(compute_tm_count))
      assert (compute_tm_count inside {2'd0,2'd1,2'd2,2'd3})
        else $error("compute_tm_count out of range");
  end

  // Truth-table coverage (all 8 input combos with corresponding output)
  always_comb begin
    if (!$isunknown({itm_valid, atm_valid, dtm_valid})) begin
      cover ({itm_valid, atm_valid, dtm_valid} == 3'b000 && compute_tm_count == 2'd0);
      cover ({itm_valid, atm_valid, dtm_valid} == 3'b001 && compute_tm_count == 2'd1);
      cover ({itm_valid, atm_valid, dtm_valid} == 3'b010 && compute_tm_count == 2'd1);
      cover ({itm_valid, atm_valid, dtm_valid} == 3'b011 && compute_tm_count == 2'd2);
      cover ({itm_valid, atm_valid, dtm_valid} == 3'b100 && compute_tm_count == 2'd1);
      cover ({itm_valid, atm_valid, dtm_valid} == 3'b101 && compute_tm_count == 2'd2);
      cover ({itm_valid, atm_valid, dtm_valid} == 3'b110 && compute_tm_count == 2'd2);
      cover ({itm_valid, atm_valid, dtm_valid} == 3'b111 && compute_tm_count == 2'd3);
    end
  end

  // Optional strictness: flag any X/Z on inputs (comment out if undesired)
  always_comb begin
    assert (!$isunknown({itm_valid, atm_valid, dtm_valid}))
      else $error("X/Z on inputs itm/atm/dtm");
  end

endmodule

// Bind into DUT
bind compute_tm_count compute_tm_count_sva u_compute_tm_count_sva (
  .atm_valid(atm_valid),
  .dtm_valid(dtm_valid),
  .itm_valid(itm_valid),
  .compute_tm_count(compute_tm_count)
);