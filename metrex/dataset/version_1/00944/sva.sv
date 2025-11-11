// SVA for binary_to_excess3 and top_module
// Bind these modules after compiling the DUT

// Assertions for the 4-bit Excess-3 converter
module b2e3_sva();
  // Within bind scope, B and E3 refer to the instance signals
  always_comb begin
    if (!$isunknown(B)) begin
      assert (E3 === (B + 4'd3))
        else $error("binary_to_excess3: E3 != (B+3) mod 16. B=%0h E3=%0h", B, E3);
      assert (!$isunknown(E3))
        else $error("binary_to_excess3: E3 has X/Z when B is known. B=%0h E3=%0h", B, E3);
    end
  end

  // Functional coverage: exercise all 16 input values
  genvar i;
  for (i=0; i<16; i++) begin : cov_b2e3
    localparam [3:0] V = i[3:0];
    always_comb cover (B == V);
  end
endmodule
bind binary_to_excess3 b2e3_sva b2e3_sva_i();


// Assertions for the top-level that stitches two converters
module top_sva();
  // Within bind scope, A, B, sum, and E refer to top_module signals
  always_comb begin
    if (!$isunknown(A) && !$isunknown(B)) begin
      assert (sum === (A + B))
        else $error("top: sum != A+B (mod 256). A=%0h B=%0h sum=%0h", A, B, sum);
      assert (E[3:0] === (sum[3:0] + 4'd3))
        else $error("top: E[3:0] incorrect. sum[3:0]=%0h E[3:0]=%0h", sum[3:0], E[3:0]);
      assert (E[7:4] === (sum[7:4] + 4'd3))
        else $error("top: E[7:4] incorrect. sum[7:4]=%0h E[7:4]=%0h", sum[7:4], E[7:4]);
      assert (E === { (sum[7:4] + 4'd3), (sum[3:0] + 4'd3) })
        else $error("top: E mismatch composite. sum=%0h E=%0h", sum, E);
      assert (!$isunknown(sum) && !$isunknown(E))
        else $error("top: X/Z on sum or E when A,B known. A=%0h B=%0h sum=%0h E=%0h", A, B, sum, E);
    end
  end

  // Coverage: all nibble values seen on sum, plus key corners
  genvar j;
  for (j=0; j<16; j++) begin : cov_nibbles
    localparam [3:0] V = j[3:0];
    always_comb cover (sum[3:0] == V);
    always_comb cover (sum[7:4] == V);
  end
  always_comb begin
    cover (sum == 8'h00);
    cover (sum == 8'hFF);
    cover (({1'b0,A} + {1'b0,B})[8]);              // detect byte overflow of A+B
    cover (sum[3:0] inside {[4'd13:4'd15]});        // low-nibble +3 carry out
    cover (sum[7:4] inside {[4'd13:4'd15]});        // high-nibble +3 carry out
  end
endmodule
bind top_module top_sva top_sva_i();