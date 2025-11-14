// SVA for MUX4X1 (binds into the DUT; uses @(*) for combinational checks)

module MUX4X1_sva();

  // Inverter and intermediate net structural correctness
  assert property (@(*)
    (not_S0 == ~S0) &&
    (not_S1 == ~S1) &&
    (not_A  == ~A)  &&
    (not_B  == ~B));

  assert property (@(*)
    (A_and_not_B       == (A  & ~B)) &&
    (not_A_and_B       == (~A &  B)) &&
    (not_A_and_not_B   == (~A & ~B)) &&
    (not_B_and_A       == (~B &  A)) &&
    (not_B_and_A       ==  A_and_not_B)); // redundancy consistency

  // Output equals gate-level SOP
  assert property (@(*)
    Z == ((A_and_not_B     & ~S1 & ~S0) |
          (not_A_and_B     &  S1 & ~S0) |
          (not_A_and_not_B &  S1 &  S0) |
          (not_B_and_A     & ~S1 &  S0)));

  // Output equals simplified behavior
  assert property (@(*)
    Z == ((~S1 & A & ~B) | (S1 & ~A & (B ^ S0))));

  // Decode sanity: S0 independence for S1=0; XOR behavior for S1=1
  assert property (@(*) (~S1) |-> (Z == (A & ~B)));
  assert property (@(*) ( S1) |-> (Z == (~A & (B ^ S0))));

  // Targeted coverage of each product term and both Z polarities
  cover property (@(*) (A  & ~B & ~S1 & ~S0) && Z);
  cover property (@(*) (A  & ~B & ~S1 &  S0) && Z);
  cover property (@(*) (~A &  B &  S1 & ~S0) && Z);
  cover property (@(*) (~A & ~B &  S1 &  S0) && Z);
  cover property (@(*) Z);
  cover property (@(*) !Z);

endmodule

bind MUX4X1 MUX4X1_sva();