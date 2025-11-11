// SVA for magnitude_comparator
// Bindable, concise, full functional checking and essential coverage

module magnitude_comparator_sva (
  input logic [3:0] a,
  input logic [3:0] b,
  input logic [1:0] out
);

  // Sample on any input/output activity; evaluate post-update with ##0
  default clocking cb @(a or b or out); endclocking

  // Compact functional spec
  let expected_cmp (logic [3:0] ax, bx) =
      (ax > bx) ? 2'b01 :
      (ax < bx) ? 2'b10 :
                  2'b00;

  // Core functional correctness (when inputs are known)
  assert property (disable iff ($isunknown({a,b})) ##0 (out == expected_cmp(a,b)))
    else $error("Comparator mapping mismatch: a=%0d b=%0d out=%b", a, b, out);

  // Output must always be a valid code (never 2'b11)
  assert property (##0 (out inside {2'b00,2'b01,2'b10}))
    else $error("Invalid out code (must be 00/01/10), out=%b a=%0d b=%0d", out, a, b);

  // If inputs are known, output must be known
  assert property ( (!$isunknown({a,b})) |-> ##0 (!$isunknown(out)) )
    else $error("Unknown out with known inputs: a=%b b=%b out=%b", a, b, out);

  // No spurious output changes without input change
  assert property ( $changed(out) |-> ($changed(a) || $changed(b)) )
    else $error("Out changed without input change: a=%0d b=%0d out=%b", a, b, out);

  // Functional coverage (essential scenarios)
  cover property (##0 (a >  b && out == 2'b01)); // a greater
  cover property (##0 (a <  b && out == 2'b10)); // b greater
  cover property (##0 (a == b && out == 2'b00)); // equal

  // Boundary/extreme cases
  cover property (##0 (a==4'd0  && b==4'd15 && out==2'b10));
  cover property (##0 (a==4'd15 && b==4'd0  && out==2'b01));
  cover property (##0 (a==b && (a==4'd0 || a==4'd15) && out==2'b00));

endmodule

// Bind into the DUT
bind magnitude_comparator magnitude_comparator_sva sva_inst (.*);