// SVA bind file for add_sub_module and adder_module
// Focus: concise, high-quality checks and key functional coverage

`ifndef ADD_SUB_SVA_SV
`define ADD_SUB_SVA_SV

// Checker bound into add_sub_module
module add_sub_module_sva;
  // Implementation consistency checks (as-coded)
  always_comb begin
    // Connectivity
    assert (inverted_b == ~b)
      else $error("add_sub_module: inverted_b != ~b");

    // Adder numeric contract (zero-extended into {carry_out,temp_sum})
    automatic logic [63:0] ext_a  = {32'd0, a};
    automatic logic [63:0] ext_ib = {32'd0, inverted_b};
    automatic logic [63:0] ext_as = ext_a + ext_ib + sub;
    assert ({carry_out, temp_sum} == ext_as)
      else $error("add_sub_module: {carry_out,temp_sum} != a + ~b + sub (zero-extended)");

    // Final sum path
    assert (sum == (temp_sum + (sub ? 32'd1 : 32'd0)))
      else $error("add_sub_module: sum != temp_sum + sub");

    // Carry vector shape implied by zero-extension in adder
    automatic logic [32:0] s33 = {1'b0, a} + {1'b0, inverted_b} + sub;
    assert (carry_out[31:1] == '0)
      else $error("add_sub_module: carry_out[31:1] must be 0");
    assert (carry_out[0] == s33[32])
      else $error("add_sub_module: carry_out[0] != carry(a + ~b + sub)");
  end

  // Specification-level checks (golden intent: sum = a ± b, 32-bit wrap)
  always_comb begin
    if (!$isunknown({a,b,sub})) begin
      automatic logic [31:0] spec_sum = a + (sub ? (~b + 32'd1) : b);
      assert (sum == spec_sum)
        else $error("SPEC FAIL: sum != a %s b", sub ? "-" : "+");
      assert (!$isunknown(sum))
        else $error("SPEC FAIL: sum is X/Z with known inputs");
      // Simple corollaries
      if (sub==1'b0 && b==32'd0) assert (sum == a)
        else if (sub==1'b0 && b==32'd0) /* no-op */ ;
      if (sub==1'b1 && a==b) assert (sum == 32'd0)
        else if (sub==1'b1 && a==b) /* no-op */ ;
    end
  end

  // Key functional coverage (single-cycle conditions)
  always_comb begin
    cover (sub==1'b0 && b==32'd0);                         // add by zero
    cover (sub==1'b1 && b==32'd0);                         // subtract zero
    cover (sub==1'b1 && a==b);                             // expected zero result
    cover (sub==1'b0 && a==32'hFFFF_FFFF && b==32'd1);     // add overflow
    cover (sub==1'b1 && a==32'd0 && b==32'd1);             // subtract borrow
  end
endmodule

// Checker bound into adder_module
module adder_module_sva;
  always_comb begin
    automatic logic [63:0] ext_a  = {32'd0, a};
    automatic logic [63:0] ext_b  = {32'd0, b};
    automatic logic [63:0] ext_as = ext_a + ext_b + carry_in;
    assert ({carry_out, sum} == ext_as)
      else $error("adder_module: {carry_out,sum} != a + b + carry_in (zero-extended)");
    assert (carry_out[31:1] == '0)
      else $error("adder_module: carry_out[31:1] must be 0");
    assert (carry_out[0] == ext_as[32])
      else $error("adder_module: carry_out[0] != carry-out bit");
    cover (carry_out[0]); // exercise carry-out
  end
endmodule

// Bind checkers
bind add_sub_module add_sub_module_sva add_sub_module_sva_i();
bind adder_module   adder_module_sva   adder_module_sva_i();

`endif