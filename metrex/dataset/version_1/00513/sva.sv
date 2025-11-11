// SVA for bin2gray
// Bind this checker to the DUT. Focused, high-quality checks + concise coverage.

module bin2gray_sva(input logic [2:0] bin,
                    input logic        reset,
                    input logic [2:0]  gray);

  // Sample on any edge of inputs (combinational DUT)
  default clocking cb @(
      posedge reset or negedge reset or
      posedge bin[0] or negedge bin[0] or
      posedge bin[1] or negedge bin[1] or
      posedge bin[2] or negedge bin[2]
  ); endclocking

  // Golden function
  function automatic logic [2:0] exp_gray(input logic [2:0] b);
    exp_gray = {b[2], b[2]^b[1], b[1]^b[0]};
  endfunction

  // No X/Z on output when inputs are known
  a_no_x:    assert property (!$isunknown({bin,reset}) |-> ##0 !$isunknown(gray));

  // Reset drives zero immediately
  a_reset:   assert property (reset |-> ##0 (gray == 3'b000));

  // Functional correctness when not in reset
  a_func:    assert property (!reset |-> ##0 (gray == exp_gray(bin)));

  // Stability: if inputs stable, output stable
  a_stable:  assert property ((bin == $past(bin) && reset == $past(reset)) |-> (gray == $past(gray)));

  // Gray distance property on +1 binary increment (no wrap)
  a_inc1:    assert property (!reset && !$past(reset) &&
                              (bin == $past(bin) + 3'd1)
                              |-> $countones(gray ^ $past(gray)) == 1);

  // Minimal coverage: see reset and every input pattern with correct mapping
  cover_reset: cover property (reset);
  generate
    genvar i;
    for (i = 0; i < 8; i++) begin : cv
      localparam logic [2:0] B = i[2:0];
      cover_bin: cover property (!reset && (bin == B) && (gray == exp_gray(B)));
    end
  endgenerate

endmodule

bind bin2gray bin2gray_sva b2g_sva_i(.bin(bin), .reset(reset), .gray(gray));