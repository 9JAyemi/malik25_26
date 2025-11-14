// SVA checker for xor_module
module xor_module_sva #(parameter W=8) (input logic [W-1:0] a, b, o);

  // Fundamental relation (4-state aware, deferred to avoid delta races)
  always_comb begin
    assert #0 (o === (a ^ b))
      else $error("XOR mismatch a=%0h b=%0h o=%0h", a, b, o);

    // No X/Z on o when inputs are known
    if (!$isunknown({a,b}))
      assert #0 (!$isunknown(o))
        else $error("o has X/Z with known inputs a=%0h b=%0h o=%0h", a, b, o);

    // Useful identities
    if (a == b)     assert #0 (o == '0)            else $error("a==b but o!=0");
    if (a == '0)    assert #0 (o == b)             else $error("a==0 but o!=b");
    if (b == '0)    assert #0 (o == a)             else $error("b==0 but o!=a");
    if (a == ~b)    assert #0 (o == {W{1'b1}})     else $error("a==~b but o!=all1");

    // Compact functional coverage
    cover (a == b);
    cover (a == '0);
    cover (b == '0);
    cover (a == ~b);
    cover ($onehot(a ^ b));
    cover ((a ^ b) == {W{1'b1}});
  end

  // Bitwise edge-direction checks (other input bit stable)
  genvar i;
  generate
    for (i = 0; i < W; i++) begin : g_bit
      // a[i] edge -> o[i] edge direction per XOR truth table
      property p_a_edge;
        @($rose(a[i]) or $fell(a[i]))
          !$changed(b[i]) |-> ($changed(o[i]) &&
                               ($rose(o[i]) == ((!b[i] && $rose(a[i])) ||
                                                ( b[i] && $fell(a[i])))));
      endproperty
      assert property (p_a_edge);

      // b[i] edge -> o[i] edge direction per XOR truth table
      property p_b_edge;
        @($rose(b[i]) or $fell(b[i]))
          !$changed(a[i]) |-> ($changed(o[i]) &&
                               ($rose(o[i]) == ((!a[i] && $rose(b[i])) ||
                                                ( a[i] && $fell(b[i])))));
      endproperty
      assert property (p_b_edge);
    end
  endgenerate
endmodule

// Bind into DUT
bind xor_module xor_module_sva #(.W(8)) xor_module_sva_b (.*);