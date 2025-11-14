// SVA for booth_multiplier
// Bind into DUT; focuses on end-to-end correctness and key micro-ops with concise coverage.

module booth_multiplier_sva (booth_multiplier dut);
  default clocking cb @(posedge dut.clk); endclocking

  bit started;
  initial started = 1'b0;
  always_ff @(posedge dut.clk) started <= 1'b1;

  // Static sanity: need ≥6 bits to hold 32
  initial assert ($bits(dut.count_reg) >= 6)
    else $error("count_reg width too small for 32 iterations");

  // Interface clean
  assert property (!$isunknown({dut.a, dut.b, dut.product}));

  // End-to-end functional correctness (signed)
  assert property ($signed(dut.product) == $signed(dut.a) * $signed(dut.b));

  // Internal mirrors/sanity
  assert property (dut.a_reg === dut.a && dut.b_reg === dut.b);
  assert property (dut.m_reg === dut.b_reg); // exposes truncation/sign-extend issue

  // Booth step micro-ops (next-state checks)
  assert property (disable iff (!started)
                   $past(dut.count_reg) > 0 && $past(dut.ac_reg[1:0]) == 2'b00
                   |=> dut.ac_reg == {$past(dut.ac_reg[30:0]), $past(dut.m_reg[31])}
                       && dut.count_reg == $past(dut.count_reg) - 1);

  assert property (disable iff (!started)
                   $past(dut.count_reg) > 0 && $past(dut.ac_reg[1:0]) == 2'b01
                   |=> dut.ac_reg == $past(dut.ac_reg) + (~$past(dut.m_reg)+1)
                       && dut.count_reg == $past(dut.count_reg) - 1);

  assert property (disable iff (!started)
                   $past(dut.count_reg) > 0 && $past(dut.ac_reg[1:0]) == 2'b10
                   |=> dut.ac_reg == $past(dut.ac_reg) + $past(dut.m_reg)
                       && dut.count_reg == $past(dut.count_reg) - 1);

  assert property (disable iff (!started)
                   $past(dut.count_reg) > 0 && $past(dut.ac_reg[1:0]) == 2'b11
                   |=> dut.ac_reg == $past(dut.ac_reg)
                       && dut.count_reg == $past(dut.count_reg) - 1);

  // Coverage: key value corners and all Booth decision patterns
  cover property (disable iff (!started) dut.a == 0 && dut.b == 0 && dut.product == 0);
  cover property (disable iff (!started) dut.a == -1 && dut.b == -1 && dut.product == 64'sd1);
  cover property (disable iff (!started) dut.a == 32'sh8000_0000 && dut.b == -1);
  cover property (disable iff (!started) dut.a == 32'sh7fff_ffff && dut.b == 32'sh7fff_ffff);

  cover property (disable iff (!started) $past(dut.count_reg) > 0 && $past(dut.ac_reg[1:0]) == 2'b00);
  cover property (disable iff (!started) $past(dut.count_reg) > 0 && $past(dut.ac_reg[1:0]) == 2'b01);
  cover property (disable iff (!started) $past(dut.count_reg) > 0 && $past(dut.ac_reg[1:0]) == 2'b10);
  cover property (disable iff (!started) $past(dut.count_reg) > 0 && $past(dut.ac_reg[1:0]) == 2'b11);
endmodule

bind booth_multiplier booth_multiplier_sva u_booth_multiplier_sva();