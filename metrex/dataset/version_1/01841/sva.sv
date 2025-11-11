// SVA for half_adder
module half_adder_sva (
  input logic x_in,
  input logic y_in,
  input logic s_out,
  input logic c_out
);
  default clocking cb @(posedge $global_clock); endclocking

  // Functional correctness; evaluate after NBA with ##0
  property ha_func;
    (!$isunknown({x_in,y_in})) |-> ##0 ({c_out,s_out} === (x_in + y_in));
  endproperty
  assert property (ha_func);

  // Safety relation (with known inputs, sum and carry cannot be 1 simultaneously)
  assert property((!$isunknown({x_in,y_in})) |-> ##0 !(s_out && c_out));

  // Input space coverage
  cover property((!$isunknown({x_in,y_in})) && {x_in,y_in}==2'b00);
  cover property((!$isunknown({x_in,y_in})) && {x_in,y_in}==2'b01);
  cover property((!$isunknown({x_in,y_in})) && {x_in,y_in}==2'b10);
  cover property((!$isunknown({x_in,y_in})) && {x_in,y_in}==2'b11);
endmodule

bind half_adder half_adder_sva ha_sva_i (
  .x_in(x_in), .y_in(y_in), .s_out(s_out), .c_out(c_out)
);


// SVA for full_adder
module full_adder_sva (
  input logic A,
  input logic B,
  input logic C_in,
  input logic S,
  input logic C_out,
  // internal structure taps
  input logic S1,
  input logic C1,
  input logic C2
);
  default clocking cb @(posedge $global_clock); endclocking

  // Functional correctness; evaluate after NBA with ##0
  property fa_func;
    (!$isunknown({A,B,C_in})) |-> ##0 ({C_out,S} === (A + B + C_in));
  endproperty
  assert property (fa_func);

  // Structural consistency with the two half_adders
  assert property((!$isunknown({A,B,C_in})) |-> ##0
                  (S1 === (A ^ B)) && (S === (S1 ^ C_in)) &&
                  (C1 === (A & B)) && (C2 === (S1 & C_in)) &&
                  (C_out === (C1 | C2)));

  // Outputs known when inputs are known
  assert property((!$isunknown({A,B,C_in})) |-> ##0 !$isunknown({S,C_out}));

  // Input space coverage (all 8 combinations)
  cover property((!$isunknown({A,B,C_in})) && {A,B,C_in}==3'b000);
  cover property((!$isunknown({A,B,C_in})) && {A,B,C_in}==3'b001);
  cover property((!$isunknown({A,B,C_in})) && {A,B,C_in}==3'b010);
  cover property((!$isunknown({A,B,C_in})) && {A,B,C_in}==3'b011);
  cover property((!$isunknown({A,B,C_in})) && {A,B,C_in}==3'b100);
  cover property((!$isunknown({A,B,C_in})) && {A,B,C_in}==3'b101);
  cover property((!$isunknown({A,B,C_in})) && {A,B,C_in}==3'b110);
  cover property((!$isunknown({A,B,C_in})) && {A,B,C_in}==3'b111);

  // Carry generation vs propagation coverage
  cover property((!$isunknown({A,B,C_in})) && (A & B) && !C_in && ##0 C_out);     // generate
  cover property((!$isunknown({A,B,C_in})) && (A ^ B) &&  C_in && ##0 C_out);     // propagate
endmodule

bind full_adder full_adder_sva fa_sva_i (
  .A(A), .B(B), .C_in(C_in), .S(S), .C_out(C_out),
  .S1(S1), .C1(C1), .C2(C2)
);