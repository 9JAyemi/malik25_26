// SVA for HilbertTransform (concise, quality-focused)
module HilbertTransform_sva #(parameter int N = 32) (
  input  logic                  clock,
  input  logic                  in,
  input  logic                  out1,
  input  logic                  out2,
  input  logic [N-1:0]          delay_line,
  input  logic [N-1:0]          coefficients,
  input  logic signed [31:0]    real_part,
  input  logic signed [31:0]    imag_part
);

  default clocking cb @ (posedge clock); endclocking

  // Basic sanity on parameterization
  initial begin
    assert (N > 1) else $error("HilbertTransform: N must be > 1");
    assert ((N % 2) == 0) else $error("HilbertTransform: N must be even");
  end

  // Past-valid
  logic past_valid;
  initial past_valid = 1'b0;
  always_ff @(posedge clock) past_valid <= 1'b1;

  // 1-bit to 32-bit signed extension helper (0/1)
  function automatic signed [31:0] ext1(input logic b);
    ext1 = b ? 32'sd1 : 32'sd0;
  endfunction

  // Coefficients are constant after init
  assert property (past_valid |-> $stable(coefficients));

  // Delay line shift behavior
  assert property (past_valid |-> delay_line[0] == $past(in));
  genvar gi;
  generate
    for (gi = 1; gi < N; gi++) begin : G_SHIFT
      assert property (past_valid |-> delay_line[gi] == $past(delay_line[gi-1]));
    end
  endgenerate

  // As-coded MAC behavior collapses to the "last pair" due to repeated NBAs
  localparam int LAST = N-2;
  assert property (past_valid |->
    real_part == ( ext1($past(delay_line[LAST    ])) * ext1($past(coefficients[LAST    ]))
                 - ext1($past(delay_line[LAST+1])) * ext1($past(coefficients[LAST+1])) ));

  assert property (past_valid |->
    imag_part == ( ext1($past(delay_line[LAST    ])) * ext1($past(coefficients[LAST+1]))
                 + ext1($past(delay_line[LAST+1])) * ext1($past(coefficients[LAST    ])) ));

  // Output mapping (width truncation)
  assert property (out1 === real_part[0]);
  assert property (out2 === imag_part[0]);

  // Knownness: if prior state was known, results are known
  assert property (past_valid && !$isunknown($past({delay_line, coefficients})))
                  |-> !$isunknown({real_part, imag_part, out1, out2});

  // Minimal but meaningful coverage
  cover property (past_valid && $changed(out1));
  cover property (past_valid && $changed(out2));

  // Show that a bit injected at 'in' reaches the tail after N cycles
  int unsigned cycles;
  initial cycles = 0;
  always_ff @(posedge clock) cycles <= cycles + 1;
  cover property (cycles >= N && delay_line[N-1] == $past(in, N));

endmodule

// Bind into DUT
bind HilbertTransform HilbertTransform_sva #(.N(N)) u_hilbert_sva (
  .clock(clock),
  .in(in),
  .out1(out1),
  .out2(out2),
  .delay_line(delay_line),
  .coefficients(coefficients),
  .real_part(real_part),
  .imag_part(imag_part)
);