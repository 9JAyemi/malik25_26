// SVA for calculator
// Bind this module to the DUT: bind calculator calculator_sva chk(.dut(this));

module calculator_sva (calculator dut);

  default clocking cb @(posedge dut.clk); endclocking
  default disable iff (dut.rst);

  // Helpers
  let sx9(x)         = {x[7], x};                                  // sign-extend to 9b
  let sx16(x)        = {{8{x[7]}}, x};                              // sign-extend to 16b
  let add9(a,b)      = $signed(sx9(a))  + $signed(sx9(b));
  let diff9(a,b)     = $signed(sx9(a))  - $signed(sx9(b));
  let prod16(a,b)    = $signed(sx16(a)) * $signed(sx16(b));
  let add_ovf(a,b)   = (add9(a,b)[8]  != add9(a,b)[7]);             // signed add overflow
  let diff_ovf(a,b)  = (diff9(a,b)[8] != diff9(a,b)[7]);            // signed sub overflow
  let prod_ovf(a,b)  = (prod16(a,b)[15:8] != {8{prod16(a,b)[7]}});  // upper not sign-ext

  // Sanity (no X on controls/outputs)
  assert property (!$isunknown({dut.op, dut.a, dut.b})); 
  assert property (!$isunknown({dut.out, dut.overflow}));

  // Reset behavior (registered)
  assert property ($past(dut.rst) |-> (dut.out==0 && dut.overflow==0));
  assert property (dut.rst && $past(dut.rst) |-> (dut.out==0 && dut.overflow==0));

  // Addition
  assert property (
    !$past(dut.rst) && $past(dut.op)==2'b00 |->
      (dut.out === add9($past(dut.a),$past(dut.b))[7:0]) &&
      (dut.overflow === add_ovf($past(dut.a),$past(dut.b)))
  );

  // Subtraction
  assert property (
    !$past(dut.rst) && $past(dut.op)==2'b01 |->
      (dut.out === diff9($past(dut.a),$past(dut.b))[7:0]) &&
      (dut.overflow === diff_ovf($past(dut.a),$past(dut.b)))
  );

  // Multiplication
  assert property (
    !$past(dut.rst) && $past(dut.op)==2'b10 |->
      (dut.out === prod16($past(dut.a),$past(dut.b))[7:0]) &&
      (dut.overflow === prod_ovf($past(dut.a),$past(dut.b)))
  );

  // Division by zero
  assert property (
    !$past(dut.rst) && $past(dut.op)==2'b11 && ($past(dut.b)==0) |->
      (dut.out==0 && dut.overflow==1)
  );

  // Division normal
  assert property (
    !$past(dut.rst) && $past(dut.op)==2'b11 && ($past(dut.b)!=0) |->
      (dut.out === ($signed($past(dut.a)) / $signed($past(dut.b)))) &&
      (dut.overflow==0)
  );

  // Functional coverage
  cover property (!$past(dut.rst) && $past(dut.op)==2'b00 &&  add_ovf($past(dut.a),$past(dut.b)));
  cover property (!$past(dut.rst) && $past(dut.op)==2'b00 && !add_ovf($past(dut.a),$past(dut.b)));
  cover property (!$past(dut.rst) && $past(dut.op)==2'b01 &&  diff_ovf($past(dut.a),$past(dut.b)));
  cover property (!$past(dut.rst) && $past(dut.op)==2'b01 && !diff_ovf($past(dut.a),$past(dut.b)));
  cover property (!$past(dut.rst) && $past(dut.op)==2'b10 &&  prod_ovf($past(dut.a),$past(dut.b)));
  cover property (!$past(dut.rst) && $past(dut.op)==2'b10 && !prod_ovf($past(dut.a),$past(dut.b)));
  cover property (!$past(dut.rst) && $past(dut.op)==2'b11 && ($past(dut.b)==0));
  cover property (!$past(dut.rst) && $past(dut.op)==2'b11 && ($past(dut.b)!=0));

endmodule