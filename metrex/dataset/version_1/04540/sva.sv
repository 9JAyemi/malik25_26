// SVA for subfxp: end-to-end functional check, stage checks, X-checks, and minimal coverage
// Bind this checker to the DUT instance(s) as shown at the bottom.

module subfxp_sva #(parameter int width = 16, cycles = 1)
(
  input  logic                     clk,
  input  logic signed [width-1:0]  a,
  input  logic signed [width-1:0]  b,
  input  logic signed [width-1:0]  q,
  // Bind to internal pipeline for stage checks and X-checks
  input  logic signed [width-1:0]  res [cycles]
);

  localparam int D = (cycles > 0) ? (cycles-1) : 0;

  // Elaboration-time parameter sanity
  initial assert (cycles >= 1)
    else $error("subfxp: cycles must be >= 1");

  default clocking cb @ (posedge clk); endclocking

  // Past-valid tracker (avoid time-0/X hazards)
  logic past_valid;
  initial past_valid = 1'b0;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // No-X/Z on key signals after first edge
  assert property (past_valid |-> !$isunknown({a,b,q}));
  genvar xi;
  generate
    for (xi = 0; xi < cycles; xi++) begin : gen_xchk
      assert property (past_valid |-> !$isunknown(res[xi]));
    end
  endgenerate

  // Structural: q mirrors last pipeline stage
  assert property (q == res[cycles-1]);

  // Stage-to-stage pipeline behavior (uses old value -> new stage)
  generate
    if (cycles > 1) begin : gen_stage_checks
      genvar i;
      for (i = 1; i < cycles; i++) begin : gen_stage
        assert property ($past(past_valid) |-> res[i] == ($past(res[i-1]) >> 1));
      end
    end
  endgenerate

  // End-to-end functional check: q equals logical right shift of (a-b) by D after D cycles
  generate
    if (D == 0) begin
      assert property (past_valid |-> q == (a - b));
    end else begin
      assert property ($past(past_valid, D) |-> q == ($past(a - b, D) >> D));
    end
  endgenerate

  // Minimal functional coverage
  cover property (past_valid && (a != b));                          // exercise subtraction
  cover property ($past(past_valid, D) && $changed(q));             // pipeline movement observed
  generate if (D > 0) begin
    cover property ($past(past_valid, D) && (($past(a-b, D) >> D) != '0)); // non-trivial shift
  end endgenerate

endmodule

// Example bind (place in a testbench or a package included by the TB)
// bind subfxp subfxp_sva #(.width(width), .cycles(cycles)) u_subfxp_sva (.* , .res(res));