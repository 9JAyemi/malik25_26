// SVA for sky130_fd_sc_ls__fahcin (full adder with inverted CIN)
// Bind into the DUT to access internal nets.
module sky130_fd_sc_ls__fahcin_sva;

  // Functional correctness (guard unknowns), evaluate after delta (##0)
  property p_sum_func;
    @(A or B or CIN) (!$isunknown({A,B,CIN})) |-> ##0 (SUM === (A ^ B ^ ~CIN));
  endproperty
  assert property (p_sum_func);

  property p_cout_func;
    @(A or B or CIN) (!$isunknown({A,B,CIN})) |-> ##0 (COUT === ((A & B) | (A & ~CIN) | (B & ~CIN)));
  endproperty
  assert property (p_cout_func);

  // Equivalent decompositions
  property p_cout_when_cin0;
    @(A or B or CIN) (!$isunknown({A,B,CIN}) && CIN==1'b0) |-> ##0 (COUT === (A | B));
  endproperty
  assert property (p_cout_when_cin0);

  property p_cout_when_cin1;
    @(A or B or CIN) (!$isunknown({A,B,CIN}) && CIN==1'b1) |-> ##0 (COUT === (A & B));
  endproperty
  assert property (p_cout_when_cin1);

  property p_sum_inv_of_norm;
    @(A or B or CIN) (!$isunknown({A,B,CIN})) |-> ##0 (SUM === ~(A ^ B ^ CIN));
  endproperty
  assert property (p_sum_inv_of_norm);

  // Internal net sanity (structural checks)
  property p_ci_not;
    @(CIN) (!$isunknown(CIN)) |-> ##0 (ci === ~CIN);
  endproperty
  assert property (p_ci_not);

  property p_xor_wire;
    @(A or B or CIN) (!$isunknown({A,B,CIN})) |-> ##0 (xor0_out_SUM === (A ^ B ^ ci));
  endproperty
  assert property (p_xor_wire);

  property p_or_wire;
    @(A or B or CIN) (!$isunknown({A,B,CIN})) |-> ##0 (or0_out_COUT === ((A & B) | (A & ci) | (B & ci)));
  endproperty
  assert property (p_or_wire);

  property p_buf_sum;
    @(xor0_out_SUM) ##0 (SUM === xor0_out_SUM);
  endproperty
  assert property (p_buf_sum);

  property p_buf_cout;
    @(or0_out_COUT) ##0 (COUT === or0_out_COUT);
  endproperty
  assert property (p_buf_cout);

  // Functional coverage: exercise all input combinations
  cover property (@(A or B or CIN) ##0 (!$isunknown({A,B,CIN}) && {A,B,CIN}==3'b000));
  cover property (@(A or B or CIN) ##0 (!$isunknown({A,B,CIN}) && {A,B,CIN}==3'b001));
  cover property (@(A or B or CIN) ##0 (!$isunknown({A,B,CIN}) && {A,B,CIN}==3'b010));
  cover property (@(A or B or CIN) ##0 (!$isunknown({A,B,CIN}) && {A,B,CIN}==3'b011));
  cover property (@(A or B or CIN) ##0 (!$isunknown({A,B,CIN}) && {A,B,CIN}==3'b100));
  cover property (@(A or B or CIN) ##0 (!$isunknown({A,B,CIN}) && {A,B,CIN}==3'b101));
  cover property (@(A or B or CIN) ##0 (!$isunknown({A,B,CIN}) && {A,B,CIN}==3'b110));
  cover property (@(A or B or CIN) ##0 (!$isunknown({A,B,CIN}) && {A,B,CIN}==3'b111));

endmodule

bind sky130_fd_sc_ls__fahcin sky130_fd_sc_ls__fahcin_sva sva_i();