// SVA for barrel_shifter (concise, port-only bind)

module barrel_shifter_sva #(parameter int W = 4, parameter int SW = $clog2(W))(
  input  logic [W-1:0] DATA,
  input  logic [SW-1:0] SHIFT,
  input  logic [W-1:0] OUT
);
  // Reference (spec): logical left shift with zero fill
  logic [W-1:0] ref;
  assign ref = (DATA << SHIFT);

  // Basic sanity: inputs/outputs shall be 0/1 only
  always @* begin
    assert (!$isunknown({DATA,SHIFT})) else
      $error("barrel_shifter: X/Z on inputs DATA=%b SHIFT=%b", DATA, SHIFT);
    if (!$isunknown({DATA,SHIFT})) begin
      assert (!$isunknown(OUT)) else
        $error("barrel_shifter: X/Z on OUT with known inputs, OUT=%b", OUT);
    end
  end

  // Functional equivalence to spec (delay a delta to avoid comb settle races)
  always @* if (!$isunknown({DATA,SHIFT})) begin
    assert (#0 (OUT == ref)) else
      $error("barrel_shifter: OUT mismatch. DATA=%b SHIFT=%0d OUT=%b REF=%b",
             DATA, SHIFT, OUT, ref);
  end

  // Useful invariants
  always @* if (!$isunknown({DATA,SHIFT})) begin
    // Zero-fill guarantee on lower SHIFT bits
    if (SHIFT != '0) assert (#0 (OUT[SHIFT-1:0] == '0)) else
      $error("barrel_shifter: zero-fill violated on lower bits. SHIFT=%0d OUT=%b",
             SHIFT, OUT);
    // No-op when SHIFT==0
    if (SHIFT == '0) assert (#0 (OUT == DATA)) else
      $error("barrel_shifter: SHIFT==0 but OUT!=DATA. DATA=%b OUT=%b", DATA, OUT);
  end

  // Minimal, targeted coverage
  always @* begin
    cover (SHIFT == 'd0);
    cover (SHIFT == 'd1);
    cover (SHIFT == 'd2);
    cover (SHIFT == 'd3);
    cover ((DATA == '0)  && (OUT == (DATA << SHIFT)));
    cover ((DATA == '1)  && (OUT == (DATA << SHIFT)));      // 0001 pattern
    cover ((DATA == 'h8) && (OUT == (DATA << SHIFT)));      // 1000 pattern
    cover ((DATA == 'hF) && (OUT == (DATA << SHIFT)));      // all ones
  end
endmodule

// Bind into DUT instances
bind barrel_shifter barrel_shifter_sva #(.W(4), .SW(2))
  barrel_shifter_sva_i (.DATA(DATA), .SHIFT(SHIFT), .OUT(OUT));