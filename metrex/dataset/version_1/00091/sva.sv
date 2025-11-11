// SVA for NAND8_reducer
// Binds into the DUT and checks both structural equations and the simplified function.
// Concise, combinational, and with essential coverage.

module NAND8_reducer_sva (
  input  logic [7:0] InY,
  input  logic       Reduced_NAND,
  input  logic       SYNTHESIZED_WIRE_0,
  input  logic       SYNTHESIZED_WIRE_1,
  input  logic       SYNTHESIZED_WIRE_2,
  input  logic       SYNTHESIZED_WIRE_3,
  input  logic       SYNTHESIZED_WIRE_4,
  input  logic       SYNTHESIZED_WIRE_5,
  input  logic       SYNTHESIZED_WIRE_6
);
  default clocking cb @(*); endclocking

  // Sanity: no X/Z on inputs/outputs/internals
  assert property (!$isunknown({InY, Reduced_NAND,
                                SYNTHESIZED_WIRE_0,SYNTHESIZED_WIRE_1,SYNTHESIZED_WIRE_2,
                                SYNTHESIZED_WIRE_3,SYNTHESIZED_WIRE_4,SYNTHESIZED_WIRE_5,
                                SYNTHESIZED_WIRE_6}))
    else $error("NAND8_reducer: X/Z detected");

  // Structural equivalence checks (as coded)
  assert property (SYNTHESIZED_WIRE_5 == ~(InY[4] | InY[5]));
  assert property (SYNTHESIZED_WIRE_4 == ~(InY[2] | InY[3]));
  assert property (SYNTHESIZED_WIRE_2 == ~InY[7]);
  assert property (SYNTHESIZED_WIRE_3 == ~(InY[0] | InY[1]));
  assert property (SYNTHESIZED_WIRE_6 == ~(InY[6] | SYNTHESIZED_WIRE_2));
  assert property (SYNTHESIZED_WIRE_0 == ~(SYNTHESIZED_WIRE_3 & SYNTHESIZED_WIRE_4));
  assert property (SYNTHESIZED_WIRE_1 == ~(SYNTHESIZED_WIRE_5 & SYNTHESIZED_WIRE_6));
  assert property (Reduced_NAND      == ~(SYNTHESIZED_WIRE_0 | SYNTHESIZED_WIRE_1));

  // Functional simplification: Reduced_NAND is 1 only when InY[6:0]==0 and InY[7]==1
  assert property (Reduced_NAND == (InY[7] & ~(|InY[6:0])));

  // Coverage: hit the unique 1-case, and exercise key internal conditions
  cover property (InY[7] & ~(|InY[6:0]) & Reduced_NAND);
  cover property (!Reduced_NAND);
  cover property (SYNTHESIZED_WIRE_3); // InY[0]==0 & InY[1]==0
  cover property (SYNTHESIZED_WIRE_4); // InY[2]==0 & InY[3]==0
  cover property (SYNTHESIZED_WIRE_5); // InY[4]==0 & InY[5]==0
  cover property (SYNTHESIZED_WIRE_6); // InY[6]==0 & InY[7]==1
endmodule

bind NAND8_reducer NAND8_reducer_sva sva_i (.*);