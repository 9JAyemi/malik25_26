// SVA checker for user_design
// Focus: functional equivalence, X-propagation, mutual exclusion, edge behavior, and concise coverage.

`ifndef USER_DESIGN_SVA
`define USER_DESIGN_SVA

module user_design_sva (
  input logic               ETH_CLK_OBUF,
  input logic               INTERNAL_RST_reg,
  input logic [7:0]         OUT1,
  input logic               IN1_ACK,
  input logic               OUT1_STB,
  input logic               IN1_STB,
  input logic               OUT1_ACK,
  input logic [7:0]         output_rs232_out
);

  default clocking cb @(posedge ETH_CLK_OBUF); endclocking

  // Core functional equivalence
  assert property (IN1_STB == (!INTERNAL_RST_reg && IN1_ACK && !OUT1_STB));
  assert property (OUT1_ACK == (!INTERNAL_RST_reg && OUT1_STB));
  assert property (output_rs232_out == ((!INTERNAL_RST_reg && OUT1_STB) ? OUT1 : 8'h00));

  // X-propagation control
  assert property (!$isunknown({INTERNAL_RST_reg, IN1_ACK, OUT1_STB}));
  assert property ((!INTERNAL_RST_reg && OUT1_STB) |-> !$isunknown(OUT1));
  assert property (!$isunknown({IN1_STB, OUT1_ACK, output_rs232_out}));

  // Mutual exclusion implied by spec (OUT1_STB gates both)
  assert property (!(IN1_STB && OUT1_ACK));

  // Edge behavior of OUT1_ACK with OUT1_STB
  assert property ((!INTERNAL_RST_reg && $rose(OUT1_STB)) |-> OUT1_ACK);
  assert property ((!INTERNAL_RST_reg && $fell(OUT1_STB)) |-> !OUT1_ACK);

  // Concise coverage: both mux legs, handshake, and edges
  cover property (!INTERNAL_RST_reg && !OUT1_STB && IN1_ACK && IN1_STB);                 // IN1_STB asserted path
  cover property (!INTERNAL_RST_reg && OUT1_STB && OUT1_ACK);                            // ACK asserted path
  cover property (!INTERNAL_RST_reg && OUT1_STB && (OUT1 != 8'h00) &&
                  (output_rs232_out == OUT1));                                           // Data pass-through (non-zero)
  cover property (!INTERNAL_RST_reg && !OUT1_STB && (output_rs232_out == 8'h00));        // Zeroed output path
  cover property (!INTERNAL_RST_reg && $rose(OUT1_STB));                                  // STB rise
  cover property (!INTERNAL_RST_reg && $fell(OUT1_STB));                                  // STB fall

endmodule

// Bind to all instances of user_design
bind user_design user_design_sva sva_i (.*);

`endif