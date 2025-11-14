// SVA for top_module. Bind this checker to the DUT.
module top_module_sva;

  // Local derived refs
  wire [1:0] ab2                  = a + b;        // {a&b, a^b}
  wire [1:0] sum_stage_sel0       = (ab2[0] + c); // (a^b) + c
  wire [1:0] carry_stage_sel1     = (ab2[1] + c); // (a&b) + c

  // Sanity/X checks
  always_comb begin
    assert (!$isunknown({a,b,c,select})) else $error("Inputs have X/Z");
    assert (!$isunknown({ha1_cout,ha1_sum,ha2_cout,ha2_sum,ha_sel,sum})) else $error("Internal/output X/Z");
  end

  // Control one-hot and mapping
  always_comb begin
    assert ($onehot(ha_sel)) else $error("ha_sel not one-hot");
    assert (ha_sel == (select ? 2'b10 : 2'b01)) else $error("ha_sel mapping mismatch");
  end

  // ha1 correctness
  always_comb begin
    assert ({ha1_cout,ha1_sum} == ab2) else $error("ha1 add mismatch");
  end

  // ha2 correctness including select mux on its 'a' input
  always_comb begin
    assert ({ha2_cout,ha2_sum} == ((ha_sel[0] ? ha1_sum : ha1_cout) + c)) else $error("ha2 add/mux mismatch");
  end

  // final_sum wiring and zero-extension to 3 bits
  always_comb begin
    assert (sum[2] == 1'b0) else $error("sum[2] must be 0 (zero-extended)");
    assert (sum[1] == (ha_sel[1] ? ha2_cout : ha1_cout)) else $error("sum[1] mismatch");
    assert (sum[0] == ha2_sum) else $error("sum[0] mismatch");
  end

  // End-to-end functional behavior per select
  always_comb begin
    if (!select) begin
      // sum == {0, a&b, (a^b)+c LSB}
      assert (sum == {1'b0, ab2[1], sum_stage_sel0[0]}) else $error("E2E mismatch for select=0");
    end else begin
      // sum == {0, ((a&b)+c) MSB, ((a&b)+c) LSB}
      assert (sum == {1'b0, carry_stage_sel1[1], carry_stage_sel1[0]}) else $error("E2E mismatch for select=1");
    end
  end

  // Minimal functional coverage
  always_comb begin
    cover (!select);
    cover (select);
    cover ({a,b,c} == 3'b000);
    cover ({a,b,c} == 3'b111);
    cover (!select && {a,b,c} == 3'b101);
    cover ( select && {a,b,c} == 3'b101);
    cover (sum == 3'b000);
    cover (sum[1] && !sum[0]);
    cover (sum[0] && !sum[1]);
  end

endmodule

bind top_module top_module_sva sva_i();