// SVA for ECC — concise, high-signal-quality checks and coverage
module ECC_SVA #(int N=1, int M=1, int P=M-N)
(
  input logic [N-1:0] in,
  input logic [M-1:0] out,
  input logic [P-1:0] parity
);

  // Sanity on parameter relationship
  initial assert (M == N + P)
    else $error("ECC SVA: M(%0d) != N(%0d)+P(%0d)", M,N,P);

  // Expected parity computation (mirrors DUT intent)
  function automatic logic parity_bit_calc (int idx, logic [N-1:0] in_bits);
    logic [N:0] tmp;
    tmp = {1'b0, in_bits};
    tmp = tmp >> ((1<<idx)-1);
    return ^tmp;
  endfunction

  function automatic logic [P-1:0] exp_parity_f (logic [N-1:0] in_bits);
    logic [P-1:0] e;
    for (int i=0; i<P; i++) e[i] = parity_bit_calc(i, in_bits);
    return e;
  endfunction

  // Combinational checks at delta-stable time
  always_comb begin
    logic [P-1:0] exp_parity = exp_parity_f(in);

    // Full codeword check
    assert #0 (out === {in, exp_parity})
      else $error("ECC SVA: out mismatch. exp=%0h got=%0h in=%0h", {in,exp_parity}, out, in);

    // Mapping check (upper bits of out are the input)
    assert #0 (out[M-1:P] === in)
      else $error("ECC SVA: out[M-1:P] != in");

    // Knownness checks
    if (!$isunknown(in)) begin
      assert #0 (!$isunknown(out))
        else $error("ECC SVA: X/Z on out with known in=%b", in);
      assert #0 (!$isunknown(parity))
        else $error("ECC SVA: X/Z on parity with known in=%b", in);
    end

    // Per-bit parity pinpointing
    for (int i=0; i<P; i++) begin
      logic exp = parity_bit_calc(i, in);
      assert #0 (out[i] === exp)
        else $error("ECC SVA: parity[%0d] exp=%0b got=%0b in=%0b", i, exp, out[i], in);
    end

    // Coverage
    cover (out === {in, exp_parity});
    for (int i=0; i<P; i++) begin
      cover (out[i]==1'b0);
      cover (out[i]==1'b1);
    end
  end
endmodule

// Bind into DUT; sizes inferred from ports
bind ECC ECC_SVA #(.N($bits(in)), .M($bits(out)), .P($bits(out)-$bits(in)))
  ecc_sva_i (.in(in), .out(out), .parity(parity));