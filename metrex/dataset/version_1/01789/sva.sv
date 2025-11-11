// SVA for adder: concise, high-quality checks and coverage
module adder_sva (
  input  logic        clk,
  input  logic        rst_n,   // tie high if no reset is available
  input  logic [3:0]  A,
  input  logic [3:0]  B,
  input  logic        C,
  input  logic [3:0]  S
);

  default clocking cb @(posedge clk); endclocking

  // helpers
  logic [4:0] wide_sum  = {1'b0,A} + {1'b0,B};
  logic [4:0] wide_diff = {1'b0,A} - {1'b0,B};
  wire  [3:0] sum_lo  = wide_sum[3:0];
  wire  [3:0] diff_lo = wide_diff[3:0];

  // past-valid for $past uses
  logic past_valid;
  always_ff @(posedge clk or negedge rst_n)
    if (!rst_n) past_valid <= 1'b0;
    else        past_valid <= 1'b1;

  // Core functional correctness (mod-16)
  assert property (disable iff (!rst_n) S == (C ? diff_lo : sum_lo));

  // No X/Z on any visible signal
  assert property (disable iff (!rst_n) !$isunknown({A,B,C,S}));

  // Key corner invariants (subset of core, aids debug)
  assert property (disable iff (!rst_n) (B == 4'd0) |-> (S == A));          // +/- 0 identity
  assert property (disable iff (!rst_n) (C == 1'b0 && A == 4'd0) |-> (S == B));
  assert property (disable iff (!rst_n) (C == 1'b1 && A == B)     |-> (S == 4'd0));

  // Stability: if inputs stable across cycles, output stable
  assert property (disable iff (!rst_n || !past_valid) $stable({A,B,C}) |-> $stable(S));

  // Functional coverage
  cover property (disable iff (!rst_n) (C == 1'b0));                    // add mode seen
  cover property (disable iff (!rst_n) (C == 1'b1));                    // sub mode seen
  cover property (disable iff (!rst_n) (C == 1'b0 && wide_sum[4]));     // add overflow wrap
  cover property (disable iff (!rst_n) (C == 1'b1 && (A < B)));         // sub underflow wrap
  cover property (disable iff (!rst_n) (C == 1'b1 && A == B && S == 0));// zero result on equal operands (sub)
  cover property (disable iff (!rst_n) (B == 0 && S == A));             // +/- zero identity
  cover property (disable iff (!rst_n) (C == 1'b0 && A == 0 && S == B));// add with zero A
  cover property (disable iff (!rst_n || !past_valid) ($rose(C) && $stable({A,B}))); // toggle to sub, same ops
  cover property (disable iff (!rst_n || !past_valid) ($fell(C) && $stable({A,B}))); // toggle to add, same ops
  cover property (disable iff (!rst_n) (S == 4'h0));
  cover property (disable iff (!rst_n) (S == 4'hF));

endmodule

// Bind example (provide a sampling clock/reset from your environment):
// bind adder adder_sva u_adder_sva (.clk(tb_clk), .rst_n(tb_rst_n), .A(A), .B(B), .C(C), .S(S));