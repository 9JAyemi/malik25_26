// SVA for multiply_complex
// Checks pipeline, reset, arithmetic, and X-propagation; adds concise coverage.

module multiply_complex_sva #(parameter WIDTH = 32)
(
  input  logic                     clk,
  input  logic                     rst_n,
  input  logic signed [WIDTH-1:0]  x,
  input  logic signed [WIDTH-1:0]  y,
  input  logic signed [2*WIDTH-1:0] z,
  input  logic signed [2*WIDTH-1:0] temp_z
);

  default clocking cb @(posedge clk); endclocking

  function automatic signed [2*WIDTH-1:0] mul2w(input signed [WIDTH-1:0] a,
                                                input signed [WIDTH-1:0] b);
    mul2w = a * b;
  endfunction

  // Reset behavior
  assert property (!rst_n |-> (temp_z == '0 && z == '0))
    else $error("multiply_complex: reset should drive temp_z/z to 0");

  // First active cycle after reset: z must still be 0 (pipeline bubble)
  assert property (rst_n && !$past(rst_n) |-> z == '0)
    else $error("multiply_complex: z not 0 on first cycle after reset deassert");

  // temp_z captures current cycle product when enabled
  assert property (rst_n |-> temp_z == mul2w(x, y))
    else $error("multiply_complex: temp_z != x*y this cycle");

  // One-cycle pipeline relation: z equals prior temp_z logically shifted
  assert property (rst_n && $past(rst_n) |-> z == ($past(temp_z) >> WIDTH))
    else $error("multiply_complex: z != ($past(temp_z) >> WIDTH)");

  // End-to-end functional relation: z equals prior product logically shifted
  assert property (rst_n && $past(rst_n) |-> z == ($past(mul2w(x, y)) >> WIDTH))
    else $error("multiply_complex: z != ($past(x*y) >> WIDTH)");

  // Logical-right-shift check: upper half of z must be zero
  assert property (rst_n && $past(rst_n) |-> z[2*WIDTH-1:WIDTH] == '0)
    else $error("multiply_complex: z upper half not zero after logical shift");

  // No X/Z after reset deasserted
  assert property (rst_n |-> !$isunknown({x, y, temp_z, z}))
    else $error("multiply_complex: X/Z detected on inputs/regs when rst_n=1");

  // Coverage
  cover property (!rst_n ##1 rst_n); // reset deassert observed

  // Zero result when either operand is zero (with 1-cycle latency)
  cover property (rst_n && $past(rst_n) &&
                  ($past(x) == 0 || $past(y) == 0) && (z == 0));

  // Positive and negative product cases seen (end-to-end with latency)
  cover property (rst_n && $past(rst_n) &&
                  ($signed($past(x)) * $signed($past(y)) > 0));
  cover property (rst_n && $past(rst_n) &&
                  ($signed($past(x)) * $signed($past(y)) < 0));

endmodule

// Bind into DUT (accesses internal temp_z)
bind multiply_complex
  multiply_complex_sva #(.WIDTH(WIDTH))
  i_multiply_complex_sva (.*);