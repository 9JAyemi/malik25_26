// SVA checker for comparator; bind this to the DUT
module comparator_sva(input logic [3:0] A, input logic [3:0] B, input logic [1:0] C);

  // Use procedural (immediate) assertions for combinational checking
  always_comb begin
    // Basic legality
    assert (C inside {2'b00,2'b01,2'b10})
      else $error("C illegal encoding: %b", C);

    // Only check functional mapping when inputs are known
    if (!$isunknown({A,B})) begin
      assert (C == {A<B, A>B})
        else $error("Comparator mismatch: A=%0d B=%0d C=%b exp=%b", A, B, C, {A<B, A>B});
    end
    else begin
      // Flag unknowns on inputs (helps catch X/Z driving compare)
      assert (0) else $error("Inputs contain X/Z: A=%b B=%b", A, B);
    end

    // Functional coverage
    cover (A==B && C==2'b00);
    cover (A>B  && C==2'b01);
    cover (A<B  && C==2'b10);

    // Boundary/extreme cases
    cover (A==4'h0 && B==4'h0 && C==2'b00);
    cover (A==4'hF && B==4'h0 && C==2'b01);
    cover (A==4'h0 && B==4'hF && C==2'b10);
  end

endmodule

// Bind to DUT instance(s)
bind comparator comparator_sva chk (.*);