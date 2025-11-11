// SVA bind module for top_module
// Focus: correctness checks and minimal yet meaningful coverage
module top_module_sva;
  // Access DUT internals through bind scope
  // Expected (golden) computations
  logic [16:0] wide_sum;
  logic [15:0] exp_add, exp_shift;
  assign wide_sum  = {1'b0, a} + {1'b0, b};
  assign exp_add   = wide_sum[15:0];
  assign exp_shift = exp_add << shift;

  // Core combinational equivalence checks
  always_comb begin
    // Basic X checks (inputs and output)
    assert (!$isunknown({a,b,shift,select})) else $error("X/Z on inputs");
    assert (!$isunknown(out))                else $error("X/Z on output");

    // Internal signal correctness
    assert (adder_out === exp_add)
      else $error("Adder mismatch: a=%h b=%h exp=%h got=%h", a, b, exp_add, adder_out);

    assert (shifter_out === exp_shift)
      else $error("Shifter mismatch: add=%h shift=%0d exp=%h got=%h", exp_add, shift, exp_shift, shifter_out);

    assert (or_out === (exp_add | exp_shift))
      else $error("OR mismatch: add=%h sh=%h exp=%h got=%h", exp_add, exp_shift, (exp_add|exp_shift), or_out);

    // Output is functionally independent of select for this RTL
    assert (out === or_out)
      else $error("Output mismatch vs or_out: out=%h or_out=%h", out, or_out);

    // End-to-end check (redundant but direct)
    assert (out === ((a + b) | ((a + b) << shift)))
      else $error("End-to-end mismatch: a=%h b=%h shift=%0d out=%h", a, b, shift, out);

    // Corner sanity
    if (shift == 0) assert (shifter_out === adder_out)
      else $error("shift==0 but shifter_out!=adder_out");
  end

  // Lightweight coverage via final assertions (ensures stimuli hit important cases)
  bit [15:0] seen_shift;
  bit [1:0]  seen_sel;
  bit        seen_carry, seen_no_carry;

  initial begin
    seen_shift   = '0;
    seen_sel     = '0;
    seen_carry   = 1'b0;
    seen_no_carry= 1'b0;
  end

  // Record coverage as simulation runs
  always @(shift)              seen_shift[shift] = 1'b1;
  always @(select)             seen_sel[select]  = 1'b1;
  always @* begin
    if (!$isunknown(wide_sum[16])) begin
      if (wide_sum[16]) seen_carry = 1'b1;
      else              seen_no_carry = 1'b1;
    end
  end

  // Require that all shift values, both select values, and both add carry/no-carry seen
  final begin
    assert (&seen_shift) else $error("Coverage: not all shift values (0..15) observed");
    assert (seen_sel == 2'b11) else $error("Coverage: both select values (0/1) not observed");
    assert (seen_carry && seen_no_carry) else $error("Coverage: add carry and no-carry both not observed");
  end
endmodule

bind top_module top_module_sva sva_top_module();