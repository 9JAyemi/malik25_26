// SVA for sky130_fd_sc_ls__fahcon (3-input full-adder with inverted carry-out)
module sky130_fd_sc_ls__fahcon_sva (
  input logic A, B, CI,
  input logic SUM, COUT_N
);

  // Sample on any input edge (combinational check at the change)
  clocking cb @(posedge A or negedge A or
                posedge B or negedge B or
                posedge CI or negedge CI);
  endclocking
  default clocking cb;

  function automatic logic exp_sum (logic a,b,ci);
    return a ^ b ^ ci;
  endfunction
  function automatic logic exp_cout_n (logic a,b,ci);
    return ~((a & b) | (a & ci) | (b & ci)); // inverted majority
  endfunction

  // Functional correctness (guarded against X/Z on inputs)
  property p_sum;
    !$isunknown({A,B,CI}) |-> ##0 (SUM    == exp_sum(A,B,CI));
  endproperty
  property p_coutn;
    !$isunknown({A,B,CI}) |-> ##0 (COUT_N == exp_cout_n(A,B,CI));
  endproperty
  // Known outputs when inputs are known
  property p_known_out;
    !$isunknown({A,B,CI}) |-> ##0 !$isunknown({SUM,COUT_N});
  endproperty

  assert property (p_sum);
  assert property (p_coutn);
  assert property (p_known_out);

  // Truth-table coverage (all 8 input combinations with expected outputs)
  cover property (A==0 && B==0 && CI==0 && SUM==0 && COUT_N==1);
  cover property (A==0 && B==0 && CI==1 && SUM==1 && COUT_N==1);
  cover property (A==0 && B==1 && CI==0 && SUM==1 && COUT_N==1);
  cover property (A==0 && B==1 && CI==1 && SUM==0 && COUT_N==0);
  cover property (A==1 && B==0 && CI==0 && SUM==1 && COUT_N==1);
  cover property (A==1 && B==0 && CI==1 && SUM==0 && COUT_N==0);
  cover property (A==1 && B==1 && CI==0 && SUM==0 && COUT_N==0);
  cover property (A==1 && B==1 && CI==1 && SUM==1 && COUT_N==0);

  // Simple toggle coverage
  cover property ($changed(SUM));
  cover property ($changed(COUT_N));

endmodule

// Bind into the DUT
bind sky130_fd_sc_ls__fahcon sky130_fd_sc_ls__fahcon_sva sva_i (.*);