// SVA for nor_gate, pwrgood_pp, and custom_module
// Bind these after compiling the DUT

// ---------------- nor_gate ----------------
module nor_gate_sva (input logic A, B, Y);
  // Functional check (use ##0 to avoid preponed sampling)
  property p_nor_func; @(A or B) ##0 (Y === ~(A | B)); endproperty
  assert property (p_nor_func);

  // Truth-table coverage
  cover property (@(A or B or Y) ##0 (!A && !B &&  Y));
  cover property (@(A or B or Y) ##0 ( A && !B && !Y));
  cover property (@(A or B or Y) ##0 (!A &&  B && !Y));
  cover property (@(A or B or Y) ##0 ( A &&  B && !Y));
endmodule

bind nor_gate nor_gate_sva u_nor_gate_sva (.A(A), .B(B), .Y(Y));


// ---------------- pwrgood_pp ----------------
module pwrgood_pp_sva (input logic A, B, C, Y);
  // Functional check
  property p_pwrgood_func; @(A or B or C) ##0 (Y === ((A & B) | C)); endproperty
  assert property (p_pwrgood_func);

  // Truth-table coverage (all 8 combinations)
  cover property (@(A or B or C or Y) ##0 (!A && !B && !C && !Y));
  cover property (@(A or B or C or Y) ##0 (!A && !B &&  C &&  Y));
  cover property (@(A or B or C or Y) ##0 (!A &&  B && !C && !Y));
  cover property (@(A or B or C or Y) ##0 (!A &&  B &&  C &&  Y));
  cover property (@(A or B or C or Y) ##0 ( A && !B && !C && !Y));
  cover property (@(A or B or C or Y) ##0 ( A && !B &&  C &&  Y));
  cover property (@(A or B or C or Y) ##0 ( A &&  B && !C &&  Y));
  cover property (@(A or B or C or Y) ##0 ( A &&  B &&  C &&  Y));
endmodule

bind pwrgood_pp pwrgood_pp_sva u_pwrgood_pp_sva (.A(A), .B(B), .C(C), .Y(Y));


// ---------------- custom_module ----------------
module custom_module_sva (
  input logic A1, A2, B1, Vdd, Gnd, X,
  input logic nor0_out, nor1_out_X, pwrgood_pp_out_X
);
  // Internal gate checks
  property p_nor0; @(A1 or A2) ##0 (nor0_out === ~(A1 | A2)); endproperty
  property p_nor1; @(B1 or nor0_out) ##0 (nor1_out_X === ~(B1 | nor0_out)); endproperty
  property p_pwrgood; @(Vdd or nor1_out_X or Gnd) ##0 (pwrgood_pp_out_X === ((Vdd & nor1_out_X) | Gnd)); endproperty
  assert property (p_nor0);
  assert property (p_nor1);
  assert property (p_pwrgood);

  // Buffer removal equivalence
  property p_x_eq_buf; @(pwrgood_pp_out_X or X) ##0 (X === pwrgood_pp_out_X); endproperty
  assert property (p_x_eq_buf);

  // End-to-end function: X = Gnd | (Vdd & ~B1 & (A1 | A2))
  property p_end_to_end;
    @(A1 or A2 or B1 or Vdd or Gnd) ##0 (X === (Gnd | (Vdd & ~B1 & (A1 | A2))));
  endproperty
  assert property (p_end_to_end);

  // Coverage of key use-cases/paths
  // Bypass via Gnd
  cover property (@(A1 or A2 or B1 or Vdd or Gnd or X) ##0 ( Gnd &&  X));
  // Vdd path via A1
  cover property (@(A1 or A2 or B1 or Vdd or Gnd or X) ##0 (!Gnd && Vdd && !B1 &&  A1 &&  X));
  // Vdd path via A2
  cover property (@(A1 or A2 or B1 or Vdd or Gnd or X) ##0 (!Gnd && Vdd && !B1 &&  A2 &&  X));
  // Forced 0 by B1
  cover property (@(A1 or A2 or B1 or Vdd or Gnd or X) ##0 (!Gnd &&  B1 && !X));
  // Forced 0 by Vdd=0
  cover property (@(A1 or A2 or B1 or Vdd or Gnd or X) ##0 (!Gnd && !Vdd && !X));
  // Forced 0 by A1=A2=0
  cover property (@(A1 or A2 or B1 or Vdd or Gnd or X) ##0 (!Gnd && !A1 && !A2 && !X));
endmodule

bind custom_module custom_module_sva u_custom_module_sva (
  .A1(A1), .A2(A2), .B1(B1), .Vdd(Vdd), .Gnd(Gnd), .X(X),
  .nor0_out(nor0_out), .nor1_out_X(nor1_out_X), .pwrgood_pp_out_X(pwrgood_pp_out_X)
);