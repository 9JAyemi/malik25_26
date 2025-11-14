// SVA for binary_to_gray. Bind this file to the DUT.
// Focus: correctness vs. spec, internal consistency, X-prop, and compact functional coverage.

module binary_to_gray_asserts;

  // Reference gray function: g = b ^ (b >> 1)
  function automatic [4:0] gray_ref (input [4:0] b);
    return b ^ {1'b0, b[4:1]};
  endfunction

  // Delay checks one delta to avoid transient ordering across always blocks
  always @* begin
    #0;

    // Internal stage-1 mapping
    assert (stage1_out[0] === bin_in[0])                    else $error("stage1_out[0] != bin_in[0]");
    assert (stage1_out[1] === (bin_in[0] ^ bin_in[1]))      else $error("stage1_out[1] mismatch");
    assert (stage1_out[2] === (bin_in[1] ^ bin_in[2]))      else $error("stage1_out[2] mismatch");
    assert (stage1_out[3] === (bin_in[2] ^ bin_in[3]))      else $error("stage1_out[3] mismatch");
    assert (stage1_out[4] === (bin_in[3] ^ bin_in[4]))      else $error("stage1_out[4] mismatch");

    // Internal stage-2 mapping
    assert (stage2_out[0] === stage1_out[0])                        else $error("stage2_out[0] mismatch");
    assert (stage2_out[1] === (stage1_out[1] ^ stage1_out[0]))      else $error("stage2_out[1] mismatch");
    assert (stage2_out[2] === (stage1_out[2] ^ stage1_out[1]))      else $error("stage2_out[2] mismatch");
    assert (stage2_out[3] === (stage1_out[3] ^ stage1_out[2]))      else $error("stage2_out[3] mismatch");
    assert (stage2_out[4] === (stage1_out[4] ^ stage1_out[3]))      else $error("stage2_out[4] mismatch");

    // Output mapping
    assert (gray_out === stage2_out)                        else $error("gray_out != stage2_out");

    // SPEC CHECK (Binary -> Gray)
    assert (gray_out === gray_ref(bin_in)) else
      $error("Gray mismatch: bin=%0b got=%0b exp=%0b", bin_in, gray_out, gray_ref(bin_in));

    // X-propagation discipline: no X on outputs when input is known
    if (!$isunknown(bin_in)) begin
      assert (!$isunknown(stage1_out)) else $error("stage1_out has X with known input");
      assert (!$isunknown(stage2_out)) else $error("stage2_out has X with known input");
      assert (!$isunknown(gray_out))   else $error("gray_out has X with known input");
    end
  end

  // Temporal sanity (immediate style): if bin increments by 1, Gray should flip one bit
  bit [4:0] prev_bin, prev_gray;
  initial begin prev_bin = 'x; prev_gray = 'x; end
  always @(bin_in or gray_out) begin
    #0;
    if (!$isunknown(prev_bin) && !$isunknown(prev_gray) && !$isunknown(bin_in) && !$isunknown(gray_out)) begin
      if (bin_in == prev_bin + 5'd1) begin
        assert ($onehot(gray_out ^ prev_gray))
          else $error("Gray should change by exactly 1 bit for consecutive bin values: prev_bin=%0d bin=%0d prev_gray=%0b gray=%0b",
                      prev_bin, bin_in, prev_gray, gray_out);
      end
    end
    prev_bin  <= bin_in;
    prev_gray <= gray_out;
  end

  // Compact functional coverage: hit every input code with correct Gray result
  genvar v;
  generate
    for (v = 0; v < 32; v++) begin : C_VALS
      always @* begin
        #0; cover (bin_in == v[4:0] && gray_out == gray_ref(v[4:0]));
      end
    end
  endgenerate

  // Bit-level toggle coverage on inputs and outputs
  genvar i;
  generate
    for (i = 0; i < 5; i++) begin : C_TOG
      bit prev_b, prev_g;
      initial begin prev_b = 'x; prev_g = 'x; end
      always @(bin_in[i]) begin
        if (!$isunknown(prev_b)) cover (bin_in[i] != prev_b);
        prev_b <= bin_in[i];
      end
      always @(gray_out[i]) begin
        if (!$isunknown(prev_g)) cover (gray_out[i] != prev_g);
        prev_g <= gray_out[i];
      end
    end
  endgenerate

endmodule

bind binary_to_gray binary_to_gray_asserts b2g_sva();