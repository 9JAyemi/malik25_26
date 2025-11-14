// SVA for priority_encoder
// Bind this module to the DUT; focuses on functional correctness, timing/registering, and coverage.

module priority_encoder_sva (
  input logic        clk,
  input logic [3:0]  D,
  input logic [1:0]  Y
);

  // Golden model of the priority encoding
  function automatic logic [1:0] enc (input logic [3:0] d);
    if (d[3])       enc = 2'b10;
    else if (d[2])  enc = 2'b01;
    else if (d[1])  enc = 2'b00;
    else if (d[0])  enc = 2'b01;
    else            enc = 2'b00;
  endfunction

  // Functional correctness: registered output matches golden map of current D
  property p_func; @(posedge clk) Y == enc(D); endproperty
  assert property (p_func);

  // Output never 2'b11 (unreachable by design)
  assert property (@(posedge clk) Y != 2'b11);

  // Bit-level check of the MSB behavior (critical priority bit)
  assert property (@(posedge clk) Y[1] == D[3]);

  // No X/Z on inputs or outputs at sampling; tighten as desired for your environment
  assert property (@(posedge clk) !$isunknown(D) && !$isunknown(Y));

  // Registered behavior: no output glitches between clock edges
  assert property (@(negedge clk) $stable(Y));

  // Functional coverage: each priority case and overshadowing seen
  cover property (@(posedge clk) D[3]);                                   // top priority active
  cover property (@(posedge clk) !D[3] && D[2]);                          // next priority
  cover property (@(posedge clk) !D[3] && !D[2] && D[1]);                 // third priority
  cover property (@(posedge clk) !D[3] && !D[2] && !D[1] && D[0]);        // lowest priority
  cover property (@(posedge clk) D == 4'b0000);                           // no requests

  // Overshadowing coverage (multiple bits set)
  cover property (@(posedge clk) D[3] && (|D[2:0]));
  cover property (@(posedge clk) !D[3] && D[2] && (|D[1:0]));
  cover property (@(posedge clk) !D[3] && !D[2] && D[1] && D[0]);

  // Output value coverage
  cover property (@(posedge clk) Y == 2'b10);
  cover property (@(posedge clk) Y == 2'b01);
  cover property (@(posedge clk) Y == 2'b00);

endmodule

// Bind to all instances of priority_encoder (ports match by name)
bind priority_encoder priority_encoder_sva sva_i (.*);