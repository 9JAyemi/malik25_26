// SVA checker for freq_divider
module freq_divider_sva #(
  parameter int M = 12,
  parameter int N = $clog2(M)
) (
  input  logic             clk_in,
  input  logic             clk_out,
  input  logic [N-1:0]     divcounter
);

  localparam int P2N  = 1 << N;
  localparam int HALF = 1 << (N-1);

  // Static parameter sanity
  initial begin
    assert (M >= 2) else $fatal(1, "freq_divider: M must be >= 2");
    assert (HALF < M) else $fatal(1, "freq_divider: 2^(N-1) must be < M");
    assert (M <= P2N) else $fatal(1, "freq_divider: M must be <= 2^N");
  end

  default clocking cb @(posedge clk_in); endclocking

  // X/Z checks
  assert property (!$isunknown(divcounter));
  assert property (!$isunknown(clk_out));

  // Counter stays within 0..M-1
  assert property (divcounter < M);

  // Next-state behavior
  assert property (disable iff ($initstate)
                   $past(divcounter) != M-1 |=> divcounter == $past(divcounter) + 1);
  assert property (disable iff ($initstate)
                   $past(divcounter) == M-1 |=> divcounter == '0);

  // Output equals MSB of counter
  assert property (clk_out == (divcounter >= HALF));

  // Edge alignment with counter value
  assert property ($rose(clk_out) |-> divcounter == HALF);
  assert property ($fell(clk_out) |-> divcounter == '0);

  // Exact low/high phase lengths and period
  assert property ($fell(clk_out) |-> !clk_out[* (HALF)] ##1 $rose(clk_out));
  assert property ($rose(clk_out) |->  clk_out[* (M-HALF)] ##1 $fell(clk_out));
  assert property ($rose(clk_out) |-> ##M $rose(clk_out));

  // Coverage
  cover property (disable iff ($initstate) $past(divcounter)==M-1 |=> divcounter=='0);
  cover property ($rose(clk_out));
  cover property ($fell(clk_out));
  cover property ($rose(clk_out) ##M $rose(clk_out));

endmodule

// Bind the checker to the DUT
bind freq_divider
  freq_divider_sva #(.M(M), .N(N))
  freq_divider_sva_i (
    .clk_in     (clk_in),
    .clk_out    (clk_out),
    .divcounter (divcounter)
  );