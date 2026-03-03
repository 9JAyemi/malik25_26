// Bindable SVA checker for sky130_fd_sc_ls__fahcon
module sky130_fd_sc_ls__fahcon_sva(input logic A, B, CI, SUM, COUT_N);

  // Functional correctness (only check when inputs are 0/1)
  assert property (@(A or B or CI)
    !$isunknown({A,B,CI}) |-> (SUM == (A ^ B ^ CI))
  ) else $error("SUM != A^B^CI");

  assert property (@(A or B or CI)
    !$isunknown({A,B,CI}) |-> (COUT_N == ~((A & B) | (A & CI) | (B & CI)))
  ) else $error("COUT_N != ~(A&B | A&CI | B&CI)");

  // Outputs must not be X/Z when inputs are 0/1
  assert property (@(A or B or CI)
    !$isunknown({A,B,CI}) |-> !$isunknown({SUM,COUT_N})
  ) else $error("Outputs X/Z with clean inputs");

  // Coverage: exercise all input combinations
  cover property (@(A or B or CI) (A==0 && B==0 && CI==0));
  cover property (@(A or B or CI) (A==0 && B==0 && CI==1));
  cover property (@(A or B or CI) (A==0 && B==1 && CI==0));
  cover property (@(A or B or CI) (A==0 && B==1 && CI==1));
  cover property (@(A or B or CI) (A==1 && B==0 && CI==0));
  cover property (@(A or B or CI) (A==1 && B==0 && CI==1));
  cover property (@(A or B or CI) (A==1 && B==1 && CI==0));
  cover property (@(A or B or CI) (A==1 && B==1 && CI==1));

  // Coverage: output toggles
  cover property (@(posedge SUM) 1);
  cover property (@(negedge SUM) 1);
  cover property (@(posedge COUT_N) 1);
  cover property (@(negedge COUT_N) 1);

endmodule

bind sky130_fd_sc_ls__fahcon sky130_fd_sc_ls__fahcon_sva u_fahcon_sva(.*);


// Optional structural checker (binds to internal nets present in this gate-level DUT)
module sky130_fd_sc_ls__fahcon_struct_sva(
  input logic A, B, CI, SUM, COUT_N,
  input logic xor0_out_SUM, a_b, a_ci, b_ci, or0_out_coutn
);
  assert property (@(A or B or CI or xor0_out_SUM))
    xor0_out_SUM == (A ^ B ^ CI)
  else $error("xor0_out_SUM wrong");

  assert property (@(A or B or a_b))
    a_b == ~(A | B)
  else $error("a_b wrong");

  assert property (@(A or CI or a_ci))
    a_ci == ~(A | CI)
  else $error("a_ci wrong");

  assert property (@(B or CI or b_ci))
    b_ci == ~(B | CI)
  else $error("b_ci wrong");

  assert property (@(a_b or a_ci or b_ci or or0_out_coutn))
    or0_out_coutn == (a_b | a_ci | b_ci)
  else $error("or0_out_coutn wrong");

  assert property (@(xor0_out_SUM or SUM))
    SUM == xor0_out_SUM
  else $error("SUM buffer mismatch");

  assert property (@(or0_out_coutn or COUT_N))
    COUT_N == or0_out_coutn
  else $error("COUT_N buffer mismatch");
endmodule

bind sky130_fd_sc_ls__fahcon sky130_fd_sc_ls__fahcon_struct_sva u_fahcon_struct_sva
  (.A(A), .B(B), .CI(CI), .SUM(SUM), .COUT_N(COUT_N),
   .xor0_out_SUM(xor0_out_SUM), .a_b(a_b), .a_ci(a_ci), .b_ci(b_ci), .or0_out_coutn(or0_out_coutn));