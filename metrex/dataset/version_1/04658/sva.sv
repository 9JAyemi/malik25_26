// SVA for full_adder_en
// Bind this module to DUT: bind full_adder_en full_adder_en_sva sva (.*);

module full_adder_en_sva (input A, B, Cin, En, Sum, Cout);

  wire [1:0] add = A + B + Cin;

  // Functional correctness (use ##0 to sample after NBA updates)
  property p_en_true_func;
    @(A or B or Cin or En or Sum or Cout)
      (! $isunknown({A,B,Cin,En}) && En) |-> ##0 {Cout,Sum} == add;
  endproperty
  assert property (p_en_true_func)
    else $error("En=1: {Cout,Sum} != A+B+Cin");

  property p_en_false_zero;
    @(A or B or Cin or En or Sum or Cout)
      (! $isunknown(En) && !En) |-> ##0 {Cout,Sum} == 2'b00;
  endproperty
  assert property (p_en_false_zero)
    else $error("En=0: outputs not zero");

  // No X/Z on outputs when inputs and En are known
  property p_no_x_outputs_when_inputs_known;
    @(A or B or Cin or En or Sum or Cout)
      (! $isunknown({A,B,Cin,En})) |-> ##0 ! $isunknown({Sum,Cout});
  endproperty
  assert property (p_no_x_outputs_when_inputs_known)
    else $error("Known inputs -> outputs must be known");

  // Edge-specific checks
  property p_posedge_en_updates;
    @(posedge En) (! $isunknown({A,B,Cin})) |-> ##0 {Cout,Sum} == add;
  endproperty
  assert property (p_posedge_en_updates)
    else $error("posedge En: {Cout,Sum} != A+B+Cin");

  property p_negedge_en_zeroes;
    @(negedge En) ##0 {Cout,Sum} == 2'b00;
  endproperty
  assert property (p_negedge_en_zeroes)
    else $error("negedge En: outputs not zero");

  // When disabled, input changes must not move outputs from zero
  property p_inputs_change_while_disabled_hold_zero;
    @(A or B or Cin) (! $isunknown(En) && !En) |-> ##0 {Cout,Sum} == 2'b00;
  endproperty
  assert property (p_inputs_change_while_disabled_hold_zero)
    else $error("En=0: outputs changed from zero");

  // Coverage
  cover property (@(posedge En) 1);
  cover property (@(negedge En) 1);

  // All input combinations when enabled
  cover property (@(A or B or Cin or En) (En && ! $isunknown({A,B,Cin}) && {A,B,Cin}==3'b000) ##0 {Cout,Sum}==2'b00);
  cover property (@(A or B or Cin or En) (En && ! $isunknown({A,B,Cin}) && {A,B,Cin}==3'b001) ##0 {Cout,Sum}==2'b01);
  cover property (@(A or B or Cin or En) (En && ! $isunknown({A,B,Cin}) && {A,B,Cin}==3'b010) ##0 {Cout,Sum}==2'b01);
  cover property (@(A or B or Cin or En) (En && ! $isunknown({A,B,Cin}) && {A,B,Cin}==3'b011) ##0 {Cout,Sum}==2'b10);
  cover property (@(A or B or Cin or En) (En && ! $isunknown({A,B,Cin}) && {A,B,Cin}==3'b100) ##0 {Cout,Sum}==2'b01);
  cover property (@(A or B or Cin or En) (En && ! $isunknown({A,B,Cin}) && {A,B,Cin}==3'b101) ##0 {Cout,Sum}==2'b10);
  cover property (@(A or B or Cin or En) (En && ! $isunknown({A,B,Cin}) && {A,B,Cin}==3'b110) ##0 {Cout,Sum}==2'b10);
  cover property (@(A or B or Cin or En) (En && ! $isunknown({A,B,Cin}) && {A,B,Cin}==3'b111) ##0 {Cout,Sum}==2'b11);

endmodule

// Example bind (place in a separate file or testbench):
// bind full_adder_en full_adder_en_sva sva (.*);