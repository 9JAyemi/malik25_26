// SVA for and_gate and its submodules. Bind these into the DUT.

module and_gate_sva(
  input logic a,
  input logic b,
  input logic out,
  input logic nand_out,
  input logic inv_out
);
  default clocking cb @(*); endclocking

  // Sanity
  assert property (!$isunknown({a,b,out,nand_out,inv_out}));

  // Functional correctness (end-to-end and by stage)
  assert property (out      === (a & b));
  assert property (nand_out === ~(a & b));
  assert property (inv_out  === ~nand_out);
  assert property (out      === inv_out);

  // Truth table coverage
  cover property (a==0 && b==0 && out==0);
  cover property (a==0 && b==1 && out==0);
  cover property (a==1 && b==0 && out==0);
  cover property (a==1 && b==1 && out==1);

  // Toggle coverage (inputs and all observables)
  cover property ($rose(a));     cover property ($fell(a));
  cover property ($rose(b));     cover property ($fell(b));
  cover property ($rose(out));   cover property ($fell(out));
  cover property ($rose(nand_out)); cover property ($fell(nand_out));
  cover property ($rose(inv_out));  cover property ($fell(inv_out));
endmodule


module nand_gate_sva(
  input logic a,
  input logic b,
  input logic out
);
  default clocking cb @(*); endclocking
  assert property (!$isunknown({a,b,out}));
  assert property (out === ~(a & b));

  // Truth table coverage
  cover property (a==0 && b==0 && out==1);
  cover property (a==0 && b==1 && out==1);
  cover property (a==1 && b==0 && out==1);
  cover property (a==1 && b==1 && out==0);
endmodule


module inverter_sva(
  input logic in,
  input logic out
);
  default clocking cb @(*); endclocking
  assert property (!$isunknown({in,out}));
  assert property (out === ~in);

  // Functional coverage
  cover property (in==0 && out==1);
  cover property (in==1 && out==0);
  cover property ($rose(in));   cover property ($fell(in));
  cover property ($rose(out));  cover property ($fell(out));
endmodule


// Bind statements
bind and_gate   and_gate_sva   sva_and_gate   (.a(a), .b(b), .out(out), .nand_out(nand_out), .inv_out(inv_out));
bind nand_gate  nand_gate_sva  sva_nand_gate  (.a(a), .b(b), .out(out));
bind inverter   inverter_sva   sva_inverter   (.in(in), .out(out));