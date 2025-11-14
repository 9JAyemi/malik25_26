// SVA for mem_encrypt_decrypt
// Bind this module to the DUT: bind mem_encrypt_decrypt mem_encrypt_decrypt_sva #(.n(n),.k(k)) sva_i(.*);

module mem_encrypt_decrypt_sva #(parameter int n=16, k=8)
(
  input  logic [n-1:0] data_in,
  input  logic [k-1:0] key_in,
  input  logic         mode,
  input  logic [n-1:0] data_out
);

  // Normalize key to n bits (truncate or zero-extend)
  wire [n-1:0] key_n = (k>=n) ? key_in[n-1:0] : {{(n-k){1'b0}}, key_in};

  // Functional correctness: output equals data_in XOR normalized key (independent of mode)
  // Guard against X/Z on inputs to avoid vacuous failures
  property p_func;
    (!$isunknown({data_in, key_in})) |-> (data_out == (data_in ^ key_n));
  endproperty
  assert property (@(data_in or key_in or mode) p_func)
    else $error("mem_encrypt_decrypt: data_out != data_in ^ key");

  // Equivalently, XORing output with key recovers input (helpful cross-check)
  property p_inverse;
    (!$isunknown({data_in, key_in})) |-> ((data_out ^ key_n) == data_in);
  endproperty
  assert property (@(data_in or key_in or mode) p_inverse)
    else $error("mem_encrypt_decrypt: (data_out ^ key) != data_in");

  // Output does not depend on mode when inputs are stable
  assert property (@(posedge mode or negedge mode)
                   !$isunknown({data_in, key_in}) && $stable(data_in) && $stable(key_in) |-> $stable(data_out))
    else $error("mem_encrypt_decrypt: data_out changed on mode toggle with stable inputs");

  // Knownness: if all inputs known, output must be known
  assert property (@(data_in or key_in or mode)
                   (!$isunknown({data_in, key_in, mode})) |-> !$isunknown(data_out))
    else $error("mem_encrypt_decrypt: Unknown output with known inputs");

  // If key narrower than data, upper bits must pass through unchanged
  generate if (k < n) begin : g_pad_check
    assert property (@(data_in or key_in or mode)
                     data_out[n-1:k] == data_in[n-1:k])
      else $error("mem_encrypt_decrypt: Upper data bits altered when key is narrower");
  end endgenerate

  // If key wider than data, changes in upper (unused) key bits must not affect output
  generate if (k > n) begin : g_unused_key_check
    assert property (@(key_in[k-1:n])
                     $stable({data_in, mode, key_in[n-1:0]}) |-> $stable(data_out))
      else $error("mem_encrypt_decrypt: Upper key bits affected data_out");
  end endgenerate

  // Minimal functional coverage
  // Cover both mode edges
  cover property (@(posedge mode) 1'b1);
  cover property (@(negedge mode) 1'b1);

  // Cover zero key (pass-through)
  cover property (@(data_in or key_in or mode) (key_in == '0) && (data_out == data_in));

  // Cover all-ones effective key (bitwise invert when key_n is all 1s)
  cover property (@(data_in or key_in or mode) (key_n == {n{1'b1}}) && (data_out == ~data_in));

  // Cover case where data_out is all zeros (i.e., key_n == data_in)
  cover property (@(data_in or key_in or mode) (key_n == data_in) && (data_out == '0));

endmodule