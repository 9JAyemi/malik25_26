// SVA for bit_counter – concise, high-quality checks and coverage
// Bind into DUT to access internal shift_reg
bind bit_counter bit_counter_sva #(.WIDTH(32)) u_bit_counter_sva (
  .CLK(CLK),
  .RST(RST),
  .data_in(data_in),
  .count_set_bits(count_set_bits),
  .shift_reg(shift_reg)
);

module bit_counter_sva #(parameter int WIDTH = 32) (
  input logic                 CLK,
  input logic                 RST,
  input logic [WIDTH-1:0]     data_in,
  input logic [4:0]           count_set_bits,
  input logic [WIDTH-1:0]     shift_reg
);

  // Compile-time sanity: output width must hold 0..WIDTH
  initial begin
    assert ($bits(count_set_bits) >= $clog2(WIDTH+1))
      else $error("bit_counter: count_set_bits width %0d < required %0d for WIDTH=%0d",
                  $bits(count_set_bits), $clog2(WIDTH+1), WIDTH);
  end

  // Global X checks
  assert property (@(posedge CLK) !$isunknown(RST))
    else $error("RST is X/Z");

  // Asynchronous reset behavior (must be cleared whenever RST==0)
  assert property (@(posedge CLK) !RST |-> (shift_reg == '0 && count_set_bits == '0))
    else $error("Not cleared during async reset");

  // While in reset, hold at zero
  assert property (@(posedge CLK) !RST |-> ($stable(shift_reg) && $stable(count_set_bits)))
    else $error("Signals not stable while in reset");

  // Establish default clocking and reset for functional checks
  default clocking cb @(posedge CLK); endclocking
  default disable iff (!RST)

  // Pipeline sample: shift_reg must capture prior data_in
  assert property (shift_reg == $past(data_in, 1, !RST))
    else $error("shift_reg != $past(data_in)");

  // Functional correctness: output equals popcount of prior data_in
  assert property (count_set_bits == $countones($past(data_in, 1, !RST)))
    else $error("count_set_bits mismatch vs $countones($past(data_in))");

  // Optional cross-check via shift_reg equivalence (redundant but localizes failures)
  assert property (count_set_bits == $countones(shift_reg))
    else $error("count_set_bits mismatch vs $countones(shift_reg)");

  // Outputs must never be X/Z when not in reset
  assert property (!$isunknown(shift_reg) && !$isunknown(count_set_bits))
    else $error("X/Z detected on internal/output signals");

  // Basic functional covers
  cover property ($countones($past(data_in, 1, !RST)) == 0  && count_set_bits == 0);
  cover property ($countones($past(data_in, 1, !RST)) == 1  && count_set_bits == 1);
  cover property ($countones($past(data_in, 1, !RST)) == 16 && count_set_bits == 16);
  cover property ($countones($past(data_in, 1, !RST)) == 31 && count_set_bits == 31);
  // This cover also exposes width issues if output cannot represent 32
  cover property ($countones($past(data_in, 1, !RST)) == 32 && count_set_bits == 32);

  // Reset sequence coverage
  cover property (RST ##1 !RST ##1 RST);

endmodule