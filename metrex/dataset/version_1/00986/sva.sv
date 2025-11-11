// SVA for reverse_bits. Bind this to the DUT.
module reverse_bits_sva (
  input [7:0] input_vector,
  input [7:0] output_vector
);
  function automatic [7:0] bitrev8 (input [7:0] x);
    bitrev8 = '0;
    for (int i = 0; i < 8; i++) bitrev8[i] = x[7-i];
  endfunction

  always_comb begin
    // Core functional check
    assert (output_vector === bitrev8(input_vector))
      else $error("reverse_bits mismatch: in=%0b out=%0b exp=%0b",
                  input_vector, output_vector, bitrev8(input_vector));

    // X-prop hygiene: known in => known out
    if (!$isunknown(input_vector)) begin
      assert (!$isunknown(output_vector))
        else $error("reverse_bits produced X/Z: in=%0b out=%0b",
                    input_vector, output_vector);
    end

    // Corner/feature coverage
    cover (input_vector == 8'h00 && output_vector == 8'h00);
    cover (input_vector == 8'hFF && output_vector == 8'hFF);
    cover (input_vector == output_vector && !$isunknown(input_vector)); // palindromic patterns

    // Per-bit mapping exercised
    for (int k = 0; k < 8; k++) begin
      cover (input_vector == (8'b1 << k) &&
             output_vector == (8'b1 << (7-k)));
    end
  end
endmodule

bind reverse_bits reverse_bits_sva u_reverse_bits_sva (.*);