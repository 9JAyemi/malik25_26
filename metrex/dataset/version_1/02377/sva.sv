// SVA checker for encrypt_module
// - Uses immediate assertions for a purely combinational DUT
// - Verifies each internal stage and end-to-end result
// - Covers corner cases including overflows and boundaries

module encrypt_module_sva (
  input  [15:0] input_data,
  input  [15:0] encrypted_output,
  input  [7:0]  A,
  input  [7:0]  B,
  input  [7:0]  A_mult,
  input  [7:0]  B_mult,
  input  [7:0]  A_plus_B_mult,
  input  [7:0]  B_plus_A_mult
);
  // Helper functions for 8-bit truncation of wider math
  function automatic [7:0] trunc8(input logic [63:0] v); trunc8 = v[7:0]; endfunction

  // Continuous combinational checks
  always_comb begin
    // Partitioning
    assert (A === input_data[15:8]) else $error("A mismatch");
    assert (B === input_data[7:0])  else $error("B mismatch");

    // Multiplies (8-bit truncation of full product)
    assert (A_mult === trunc8(A*32'd3)) else $error("A_mult mismatch");
    assert (B_mult === trunc8(B*32'd5)) else $error("B_mult mismatch");

    // Adds (8-bit truncation of sum)
    assert (A_plus_B_mult === trunc8(A_mult + B)) else $error("A_plus_B_mult mismatch");
    assert (B_plus_A_mult === trunc8(B_mult + A)) else $error("B_plus_A_mult mismatch");

    // End-to-end output formatting
    assert (encrypted_output === {A_plus_B_mult, B_plus_A_mult})
      else $error("encrypted_output mismatch");

    // If inputs are fully known, all derived signals must be known
    if (!$isunknown(input_data)) begin
      assert (!$isunknown({A,B,A_mult,B_mult,A_plus_B_mult,B_plus_A_mult,encrypted_output}))
        else $error("Unexpected X/Z on internal/output with known input");
    end

    // Minimal but meaningful coverage
    cover (input_data == 16'h0000);
    cover (input_data == 16'hFFFF);
    cover (A == 8'h00 && B == 8'hFF);
    cover (A == 8'hFF && B == 8'h00);

    // Overflow/wrap coverage on operations
    cover ((A*32'd3) > 32'd255);            // A_mult overflow before truncation
    cover ((B*32'd5) > 32'd255);            // B_mult overflow before truncation
    cover ((A_mult + B) > 9'd255);          // A_plus_B_mult overflow before truncation
    cover ((B_mult + A) > 9'd255);          // B_plus_A_mult overflow before truncation

    // Interesting output patterns
    cover (A_plus_B_mult == 8'h00);
    cover (B_plus_A_mult == 8'h00);
  end
endmodule

// Optional: port-only end-to-end checker (no internal nets required)
module encrypt_module_e2e_sva (
  input [15:0] input_data,
  input [15:0] encrypted_output
);
  function automatic [7:0] trunc8(input logic [63:0] v); trunc8 = v[7:0]; endfunction
  wire [7:0] A = input_data[15:8];
  wire [7:0] B = input_data[7:0];
  wire [7:0] hi = trunc8(trunc8(A*32'd3) + B);
  wire [7:0] lo = trunc8(trunc8(B*32'd5) + A);

  always_comb begin
    assert (encrypted_output === {hi, lo})
      else $error("E2E: encrypted_output mismatch");
    if (!$isunknown(input_data)) begin
      assert (!$isunknown(encrypted_output))
        else $error("E2E: Unexpected X/Z on output with known input");
    end

    cover (input_data == 16'h0000);
    cover (input_data == 16'hFFFF);
    cover ((A*32'd3) > 32'd255);
    cover ((B*32'd5) > 32'd255);
    cover ((trunc8(A*32'd3) + B) > 9'd255);
    cover ((trunc8(B*32'd5) + A) > 9'd255);
  end
endmodule

// Bind examples:
// Bind full internal checker (recommended for thorough stage checks)
// bind encrypt_module encrypt_module_sva sva_i (
//   .input_data(input_data),
//   .encrypted_output(encrypted_output),
//   .A(A), .B(B),
//   .A_mult(A_mult), .B_mult(B_mult),
//   .A_plus_B_mult(A_plus_B_mult), .B_plus_A_mult(B_plus_A_mult)
// );

// Or bind the port-only end-to-end checker
// bind encrypt_module encrypt_module_e2e_sva e2e_i (.*);