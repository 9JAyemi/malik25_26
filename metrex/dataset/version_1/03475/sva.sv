// SVA for CryptoBlock
// Concise, high-quality checks for functional correctness and basic coverage.

module CryptoBlock_sva #(parameter int k=128, m=256, n=256) (
  input  logic [m-1:0] plaintext,
  input  logic [k-1:0] key,
  input  logic [m-1:0] ciphertext,
  input  logic [m-1:0] message,
  input  logic [m-1:0] ciphertext_out,
  input  logic [m-1:0] plaintext_out,
  input  logic [n-1:0] hash_out
);

  // Combinational correctness (gated to avoid false trips on X/Z)
  always_comb begin
    if (!$isunknown({plaintext, key}))
      assert (ciphertext_out === (plaintext ^ key))
        else $error("ciphertext_out != plaintext ^ key");

    if (!$isunknown({ciphertext, key}))
      assert (plaintext_out === (ciphertext ^ key))
        else $error("plaintext_out != ciphertext ^ key");

    if (!$isunknown({plaintext, key}))
      assert ((ciphertext_out ^ key) === plaintext)
        else $error("Decrypt(ciphertext_out) != plaintext");

    if (!$isunknown({ciphertext, key}))
      assert ((plaintext_out ^ key) === ciphertext)
        else $error("Encrypt(plaintext_out) != ciphertext");

    if (!$isunknown({message}))
      assert (hash_out === message)
        else $error("hash_out != message");

    // Cross-consistency: XOR relation across both paths
    if (!$isunknown({plaintext, ciphertext, key}))
      assert ((ciphertext_out ^ plaintext_out) === (plaintext ^ ciphertext))
        else $error("ciphertext_out ^ plaintext_out != plaintext ^ ciphertext");

    // Outputs should be 2-state when inputs are 2-state
    if (!$isunknown({plaintext, key, ciphertext, message})) begin
      assert (!$isunknown({ciphertext_out, plaintext_out, hash_out}))
        else $error("Outputs contain X/Z with 2-state inputs");
    end
  end

  // Lightweight functional coverage of key scenarios
  always_comb begin
    cover (key == '0);
    cover (key == {k{1'b1}});
    cover (plaintext == '0);
    cover (ciphertext == '0);
    cover (message == '0);

    // Round-trip scenarios
    cover ((ciphertext_out === (plaintext ^ key)) && ((ciphertext_out ^ key) === plaintext));
    cover ((plaintext_out === (ciphertext ^ key)) && ((plaintext_out ^ key) === ciphertext));

    // Cross scenario: if ciphertext matches encrypt(plaintext), decryption returns plaintext
    cover ((ciphertext === (plaintext ^ key)) && (plaintext_out === plaintext));
    // Cross scenario: if plaintext matches decrypt(ciphertext), encryption returns ciphertext
    cover ((plaintext === (ciphertext ^ key)) && (ciphertext_out === ciphertext));
  end

endmodule

// Bind example (in a testbench or a separate file):
// bind CryptoBlock CryptoBlock_sva #(.k(k), .m(m), .n(n)) CryptoBlock_sva_i (
//   .plaintext(plaintext),
//   .key(key),
//   .ciphertext(ciphertext),
//   .message(message),
//   .ciphertext_out(ciphertext_out),
//   .plaintext_out(plaintext_out),
//   .hash_out(hash_out)
// );