// SVA checker for key_Processor
// Bind this checker to the DUT to verify combinational behavior and coverage.

module key_Processor_sva (
  input        select,
  input [63:0] key,
  input [28:1] lefto,
  input [28:1] righto
);

  // Combinational, sample after delta to let DUT settle
  always @(select or key) begin
    #0;

    // No unknowns on outputs when inputs are known
    if (!$isunknown({select, key})) begin
      assert (!$isunknown({lefto, righto})) else
        $error("key_Processor: X/Z on outputs with known inputs");

      // Pass-through mode: select == 0
      if (select == 1'b0) begin
        assert (lefto  == key[63:36]) else
          $error("key_Processor: lefto pass-through mismatch");
        assert (righto == key[35:2]) else
          $error("key_Processor: righto pass-through mismatch");
      end

      // Permutation mode: select == 1
      if (select == 1'b1) begin
        // Width-mismatch consequences (as coded): MSBs of temp are zero
        assert (lefto == 28'b0) else
          $error("key_Processor: lefto should be 0 when select=1");
        assert (righto[28:15] == 14'b0) else
          $error("key_Processor: righto[28:15] should be 0 when select=1");

        // Check mapping of 2-bit groups into righto[14:1]
        assert (righto[14:13] == key[58:57]) else
          $error("key_Processor: map mismatch righto[14:13] <- key[58:57]");
        assert (righto[12:11] == key[50:49]) else
          $error("key_Processor: map mismatch righto[12:11] <- key[50:49]");
        assert (righto[10:9]  == key[42:41]) else
          $error("key_Processor: map mismatch righto[10:9]  <- key[42:41]");
        assert (righto[8:7]   == key[34:33]) else
          $error("key_Processor: map mismatch righto[8:7]   <- key[34:33]");
        assert (righto[6:5]   == key[26:25]) else
          $error("key_Processor: map mismatch righto[6:5]   <- key[26:25]");
        assert (righto[4:3]   == key[18:17]) else
          $error("key_Processor: map mismatch righto[4:3]   <- key[18:17]");
        assert (righto[2:1]   == key[10:9])  else
          $error("key_Processor: map mismatch righto[2:1]   <- key[10:9]");
        // Note: key[2:1] are dropped (temp[1:0]) by righto slice [35:2]
      end
    end

    // Functional coverage
    cover (select == 1'b0 && lefto == key[63:36] && righto == key[35:2]);
    cover (select == 1'b1 && lefto == 28'b0 && righto[28:15] == 14'b0);
    cover (select == 1'b1 && righto[14:13] == key[58:57]);
    cover (select == 1'b1 && righto[12:11] == key[50:49]);
    cover (select == 1'b1 && righto[10:9]  == key[42:41]);
    cover (select == 1'b1 && righto[8:7]   == key[34:33]);
    cover (select == 1'b1 && righto[6:5]   == key[26:25]);
    cover (select == 1'b1 && righto[4:3]   == key[18:17]);
    cover (select == 1'b1 && righto[2:1]   == key[10:9]);
  end

endmodule

// Bind into the DUT (instantiate once per DUT instance)
bind key_Processor key_Processor_sva key_Processor_sva_i (
  .select(select),
  .key(key),
  .lefto(lefto),
  .righto(righto)
);