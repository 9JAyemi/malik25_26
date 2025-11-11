// SVA for circuit_module
// Binds into the DUT and checks internal combinational semantics concisely.

module circuit_module_sva (
  input       out,
  input       a,
  input [1:0] b,
  input [2:0] c,
  input [3:0] d,
  input [4:0] e,

  // internal DUT nets (bound by name)
  input [4:0] complement,
  input [4:0] xor_inputs,
  input       all_complement
);

  // derive a “clock” on any input change; ignore checks when inputs are X/Z
  default clocking cb @(posedge $changed({a,b,c,d,e})); endclocking
  default disable iff ($isunknown({a,b,c,d,e}));

  // Internal signal formation checks (respecting sizing/truncation semantics)
  // complement is the 5 LSBs of {~a,~b,~c,~d,~e} -> equals {~e[0],~e[1],~e[2],~e[3],~e[4]}
  assert property (1 |-> ##0 complement == {~e[0],~e[1],~e[2],~e[3],~e[4]});

  // xor_inputs is the 5 LSBs of {a,b[0],b[1],...,e[4]} -> equals {e[0],e[1],e[2],e[3],e[4]}
  assert property (1 |-> ##0 xor_inputs == {e[0],e[1],e[2],e[3],e[4]});

  // Reductions
  assert property (1 |-> ##0 all_complement == &complement);
  assert property (1 |-> ##0 (^xor_inputs) == (^e)); // parity invariant to bit order

  // Out function equals the RTL expression
  assert property (1 |-> ##0 out == (all_complement ? 1'b0 : (|complement) ? 1'b1 : ^xor_inputs));

  // Strengthened functional consequence: out is 0 only when e == 5'b00000, else 1
  assert property (1 |-> ##0 ((e == 5'b00000) ? (out == 1'b0) : (out == 1'b1)));

  // Independence from a/b/c/d (they are effectively unused by construction)
  assert property (($changed({a,b,c,d}) && $stable(e)) |-> ##0
                   $stable({complement,xor_inputs,all_complement,out}));

  // Branch coverage
  cover property (1 |-> ##0 all_complement);                    // e == 0
  cover property (1 |-> ##0 (!all_complement && |complement));  // 0 < e < all 1s
  cover property (1 |-> ##0 (~|complement));                    // e == all 1s

  // Output activity coverage
  cover property ($rose(out));
  cover property ($fell(out));

endmodule

bind circuit_module circuit_module_sva sva_i(.*);