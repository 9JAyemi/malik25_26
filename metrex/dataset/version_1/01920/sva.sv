// SVA for clk_generator
module clk_generator_sva #(parameter int BAUDRATE=8, M2=4)
(
  input logic clk,
  input logic clk_ena,
  input logic rstn,
  input logic clk_out
);
  // Bound scope visibility: divcounter (internal to DUT)
  default clocking cb @(posedge clk); endclocking
  default disable iff (!rstn);

  localparam int LAST = BAUDRATE-1;

  // Static parameter checks
  initial begin
    assert (BAUDRATE > 0) else $fatal(1, "BAUDRATE must be > 0");
    assert (M2 >= 0 && M2 < BAUDRATE) else $fatal(1, "M2 must be in [0, BAUDRATE-1]");
  end

  // Counter always in range when out of reset
  assert property (divcounter < BAUDRATE);

  // Next-state counter behavior
  // When disabled, force to LAST on next cycle
  assert property (!$past(clk_ena) |-> divcounter == LAST);

  // When enabled and not at LAST, increment by 1
  assert property ($past(clk_ena) && $past(divcounter) != LAST
                   |-> divcounter == $past(divcounter) + 1);

  // When enabled and at LAST, wrap to 0
  assert property ($past(clk_ena) && $past(divcounter) == LAST
                   |-> divcounter == 0);

  // Async reset effect sampled synchronously: if rstn was low last cycle, counter is 0 now
  assert property (disable iff (1'b0) (!$past(rstn) |-> divcounter == 0));

  // Output function: clk_out equals (prev divcounter==M2) AND prev clk_ena
  assert property (clk_out == (($past(divcounter) == M2) && $past(clk_ena)));

  // clk_out must be single-cycle pulse (no back-to-back 1s)
  assert property ($past(clk_out) |-> !clk_out);

  // No X/Z on key signals out of reset
  assert property (!$isunknown({clk_out, divcounter}));

  // Coverage
  // Two pulses separated by exactly BAUDRATE cycles (steady operation)
  cover property (clk_ena && clk_out ##[BAUDRATE] clk_out);

  // Disable -> enable transition produces counter wrap start at 0
  cover property (!clk_ena ##1 clk_ena ##1 (divcounter == 0));

  // Pulse observed at the programmed tap M2
  cover property (clk_ena && (divcounter == M2) ##1 clk_out);

endmodule

// Bind into DUT (inherits DUT parameters)
bind clk_generator clk_generator_sva #(.BAUDRATE(BAUDRATE), .M2(M2)) u_clk_generator_sva (.*);