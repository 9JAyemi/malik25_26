// SVA checkers for add_sub_pipeline and adder16bit
// Bind these into the RTL; focuses on combinational correctness, carry-chaining, and basic coverage.

module add_sub_pipeline_sva;

  // local helper computations
  logic [16:0] lo_add, hi_add;
  logic [31:0] addsub_eq;

  always_comb begin
    lo_add   = a[15:0]  + (b[15:0]  ^ {16{sub}}) + sub;
    hi_add   = a[31:16] + (b[31:16] ^ {16{sub}}) + lo_add[16];
    addsub_eq = a + (b ^ {32{sub}}) + sub;

    // Partitioning and masking
    assert (a_lo == a[15:0]) else $error("a_lo mismatch");
    assert (a_hi == a[31:16]) else $error("a_hi mismatch");
    assert (b_lo == (b[15:0]  ^ {16{sub}})) else $error("b_lo mask mismatch");
    assert (b_hi == (b[31:16] ^ {16{sub}})) else $error("b_hi mask mismatch");

    // Low-half adder carry and sum
    assert (carry  == lo_add[16])     else $error("Low-half carry mismatch");
    assert (sum_lo == lo_add[15:0])   else $error("Low-half sum mismatch");

    // High-half adder sum (with chained carry)
    assert (sum_hi == hi_add[15:0])   else $error("High-half sum mismatch");

    // Output assembly and end-to-end equivalence
    assert (sum == {sum_hi, sum_lo})  else $error("sum concatenation mismatch");
    assert (sum == addsub_eq)         else $error("End-to-end add/sub mismatch");

    // No X/Z propagation when inputs known
    if (!$isunknown({a,b,sub})) begin
      assert (!$isunknown({sum, sum_lo, sum_hi, carry, a_lo, a_hi, b_lo, b_hi}))
        else $error("X/Z detected in outputs/internals");
    end

    // Compact functional coverage
    cover (!sub);                                // add
    cover (sub);                                 // sub
    cover (lo_add[16]);                          // low-half carry
    cover (hi_add[16]);                          // high-half carry
    cover (sub && (a == b));                     // subtraction to zero
    cover (sub && (a < b));                      // borrow across 32-bit
    cover (!sub && (&a && (b==32'h1)));          // add overflow scenario
  end

endmodule

module adder16bit_sva;
  logic [16:0] sum17;

  always_comb begin
    sum17 = a + b + carry_in;

    assert ({carry_out, sum} == sum17)
      else $error("adder16bit wrong result");

    if (!$isunknown({a,b,carry_in})) begin
      assert (!$isunknown({sum,carry_out}))
        else $error("adder16bit X/Z on outputs");
    end

    cover (carry_in);
    cover (sum17[16]); // carry out
  end
endmodule

bind add_sub_pipeline add_sub_pipeline_sva add_sub_pipeline_sva_i();
bind adder16bit      adder16bit_sva      adder16bit_sva_i();