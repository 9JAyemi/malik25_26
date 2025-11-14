// SVA for scrambler
// Bind into DUT: bind scrambler scrambler_sva #(.WIDTH(WIDTH)) i_scrambler_sva (.*);

module scrambler_sva #(
  parameter int WIDTH = 512,
  parameter logic [57:0] SCRAM_INIT = 58'h3ff_ffff_ffff_ffff
)(
  input  logic                  clk,
  input  logic                  arst,
  input  logic                  ena,
  input  logic [WIDTH-1:0]      din,
  input  logic [WIDTH-1:0]      dout,
  input  logic [57:0]           scram_state
);

  initial assert (WIDTH > 0);

  default clocking cb @ (posedge clk); endclocking

  // $past validity guard
  logic past_valid;
  always @(posedge clk or posedge arst) begin
    if (arst) past_valid <= 1'b0;
    else      past_valid <= 1'b1;
  end

  // Predict history from a given state and input block
  function automatic logic [WIDTH+58-1:0]
    gen_hist(input logic [57:0] s, input logic [WIDTH-1:0] di);
    logic [WIDTH+58-1:0] h;
    int i;
    h[57:0] = s;
    for (i = 58; i < WIDTH+58; i++) begin
      h[i] = h[i-58] ^ h[i-39] ^ di[i-58];
    end
    return h;
  endfunction

  // Asynchronous reset takes effect immediately
  assert property (@(posedge arst) 1'b1 |-> ##0 (dout == '0 && scram_state == SCRAM_INIT));

  // While in reset, hold reset values
  assert property (arst |-> (dout == '0 && scram_state == SCRAM_INIT));

  // When not enabled, hold state and output
  assert property (disable iff (arst) !ena |-> ($stable(dout) && $stable(scram_state)));

  // When enabled, update matches reference model computed from previous cycle's state/input
  let hist_past = gen_hist($past(scram_state), $past(din));
  assert property (disable iff (arst)
                   past_valid && ena |-> (dout == hist_past[58 +: WIDTH]
                                        && scram_state == hist_past[WIDTH +: 58]));

  // Sanity: no X on input when enabled (helps avoid vacuous compares)
  assert property (disable iff (arst) ena |-> !$isunknown(din));

  // Coverage
  cover property (disable iff (arst) ena);
  cover property (disable iff (arst) !ena);
  cover property (disable iff (arst) ena ##1 ena);       // back-to-back updates
  cover property (disable iff (arst) !ena ##1 ena ##1 !ena);

endmodule

// Example bind (place in a package or top-level tb):
// bind scrambler scrambler_sva #(.WIDTH(WIDTH)) i_scrambler_sva (.*);