// SVA for sd_counter (Gray counter with CE, binary mirror)
// Assumes the provided defines in the DUT are active: CNT_TYPE_GRAY, CNT_Q, CNT_Q_BIN, CNT_CE

module sd_counter_sva #(parameter int N = `CNT_LENGTH)
(
  input  logic              clk,
  input  logic              rst,
  input  logic              cke,
  input  logic [N:1]        q,
  input  logic [N:1]        q_bin
);
  // Reindex to [N-1:0] for arithmetic/bit ops
  wire logic [N-1:0] qb = q_bin;
  wire logic [N-1:0] qg = q;
  localparam logic [N-1:0] MAX = {N{1'b1}};

  function automatic logic [N-1:0] gray(input logic [N-1:0] b);
    return (b >> 1) ^ b;
  endfunction

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Known values after reset deassert
  assert property (!$isunknown({qg, qb})) else $error("X/Z detected on outputs");

  // Reset behavior (checked synchronously)
  assert property (@(posedge clk) rst |-> (qg == '0 && qb == '0))
    else $error("Outputs not 0 while reset asserted");

  // Binary increment with CE (wraps naturally due to width)
  assert property (cke |-> (qb == $past(qb, 1, rst) + 1))
    else $error("q_bin failed +1 increment when cke=1");

  // Hold when CE low
  assert property (!cke |-> ($stable(qb) && $stable(qg)))
    else $error("Outputs changed while cke=0");

  // Output changes only if CE is high
  assert property ((qb != $past(qb, 1, rst)) |-> cke)
    else $error("q_bin changed without cke");
  assert property ((qg != $past(qg, 1, rst)) |-> cke)
    else $error("q (Gray) changed without cke");

  // Gray-coded relation to binary mirror (always true)
  assert property (qg == gray(qb))
    else $error("q != gray(q_bin)");

  // Gray transition: exactly 1 bit toggles when CE is high
  assert property (cke |-> $onehot(qg ^ $past(qg, 1, rst)))
    else $error("Non-1-bit Gray transition on q when cke=1");

  // Coverage

  // First count after reset deassert with cke
  cover property (@(posedge clk) $fell(rst) ##1 cke ##1 (qb == 1));

  // CE hold then count
  cover property (!rst && !cke [*2] ##1 cke ##1 1);

  // Wrap-around from MAX to 0 on next enabled cycle
  cover property (( $past(qb, 1, rst) == MAX && cke) ##1 (qb == '0));

  // Observe a Gray transition on MSB (optional but useful)
  cover property (cke && (qg[N-1] != $past(qg[N-1], 1, rst)));

endmodule

bind sd_counter sd_counter_sva #(.N(`CNT_LENGTH)) u_sd_counter_sva (
  .clk (clk),
  .rst (rst),
  .cke (cke),
  .q   (q),
  .q_bin(q_bin)
);