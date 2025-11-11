// SVA for diff_d2e: 1-cycle pipeline register with active-low async reset
// Bindable, concise, with reset checks, transfer checks, X-checks, and basic coverage.

// synthesis translate_off
module diff_d2e_sva (
  input clk, clrn,
  // inputs
  input wreg, m2reg, shift, aluimm, wmem, wzero,
  input [3:0]  aluc,
  input [4:0]  rd,
  input [31:0] qa, qb, eximme,
  // outputs (observed as inputs to this checker)
  input ewreg, em2reg, eshift, ealuimm, ewmem, ewzero,
  input [3:0]  ealuc,
  input [4:0]  erd, esa,
  input [31:0] eqa, eqb, eeximme
);

  default clocking @(posedge clk); endclocking
  default disable iff (!clrn);

  // 1. Async reset clears all outputs immediately on negedge clrn
  property p_async_reset_clears;
    @(negedge clrn)
      1 |-> ( {ewreg,em2reg,eshift,ealuimm,ewmem,ewzero} == 6'b0
              && ealuc == 4'b0 && erd == 5'b0 && esa == 5'b0
              && eqa == 32'b0 && eqb == 32'b0 && eeximme == 32'b0 );
  endproperty
  assert property (p_async_reset_clears);

  // 2. While reset is held low, outputs stay 0
  assert property (@(posedge clk) !clrn |-> (
      {ewreg,em2reg,eshift,ealuimm,ewmem,ewzero} == 6'b0
      && ealuc == 4'b0 && erd == 5'b0 && esa == 5'b0
      && eqa == 32'b0 && eqb == 32'b0 && eeximme == 32'b0 ));

  // 3. One-cycle registered transfer when not in or just exiting reset
  //    (require previous cycle also out of reset)
  property p_one_cycle_pipe;
    clrn && $past(clrn) |->
      {ewreg,em2reg,eshift,ealuimm,ewmem,ewzero,ealuc,erd,eqa,eqb,eeximme}
      == $past({wreg,m2reg,shift,aluimm,wmem,wzero,aluc,rd,qa,qb,eximme});
  endproperty
  assert property (p_one_cycle_pipe);

  // 4. esa must always be 0 (wired constant in DUT)
  assert property (esa == 5'b0);

  // 5. No X/Z on outputs when out of reset
  assert property (!$isunknown({ewreg,em2reg,eshift,ealuimm,ewmem,ewzero,
                                ealuc,erd,esa,eqa,eqb,eeximme}));

  // Coverage: see reset activity and a transfer event
  cover property (@(negedge clrn) 1);
  cover property (@(posedge clk) disable iff(!clrn)
    $changed({wreg,m2reg,shift,aluimm,wmem,wzero,aluc,rd,qa,qb,eximme})
    ##1 {ewreg,em2reg,eshift,ealuimm,ewmem,ewzero,ealuc,erd,eqa,eqb,eeximme}
        == $past({wreg,m2reg,shift,aluimm,wmem,wzero,aluc,rd,qa,qb,eximme}) );

endmodule

bind diff_d2e diff_d2e_sva sva_diff_d2e (.*);
// synthesis translate_on