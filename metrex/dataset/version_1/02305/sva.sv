// SVA for OAI21X1
// Binds assertions to the DUT; focuses on functional correctness and power behavior.

bind OAI21X1 OAI21X1_sva oai21x1_sva_i (.*);

module OAI21X1_sva (input logic IN1, IN2, IN3, QN, VDD, VSS);

  // Combinational sample on any relevant change
  localparam dummy = 0; // placate tools if empty params disliked
  let pwr_good = (VDD === 1'b1) && (VSS === 1'b0);
  let in_known = !$isunknown({IN1, IN2, IN3});
  // Derived function under good power:
  // QN = (IN1 | IN2) & (~IN2 | ~IN3)
  let func = (IN1 | IN2) & ((~IN2) | (~IN3));

  // Functional correctness under good power and known inputs
  assert property (@(IN1 or IN2 or IN3 or VDD or VSS)
                   pwr_good && in_known |-> (QN === func))
    else $error("OAI21X1: Functional mismatch under pwr_good.");

  // Output clamps low if any power is bad (explicit safe cases)
  assert property (@(IN1 or IN2 or IN3 or VDD or VSS)
                   (VDD === 1'b0) |-> (QN === 1'b0))
    else $error("OAI21X1: QN not low when VDD=0.");
  assert property (@(IN1 or IN2 or IN3 or VDD or VSS)
                   (VSS === 1'b1) |-> (QN === 1'b0))
    else $error("OAI21X1: QN not low when VSS=1.");

  // No X/Z on output when power good and inputs known
  assert property (@(IN1 or IN2 or IN3 or VDD or VSS)
                   pwr_good && in_known |-> !$isunknown(QN))
    else $error("OAI21X1: QN unknown under pwr_good with known inputs.");

  // Minimal coverage
  // - Exercise all input combinations under good power
  cover property (@(IN1 or IN2 or IN3)
                  pwr_good && in_known && {IN1,IN2,IN3} == 3'b000);
  cover property (@(IN1 or IN2 or IN3)
                  pwr_good && in_known && {IN1,IN2,IN3} == 3'b001);
  cover property (@(IN1 or IN2 or IN3)
                  pwr_good && in_known && {IN1,IN2,IN3} == 3'b010);
  cover property (@(IN1 or IN2 or IN3)
                  pwr_good && in_known && {IN1,IN2,IN3} == 3'b011);
  cover property (@(IN1 or IN2 or IN3)
                  pwr_good && in_known && {IN1,IN2,IN3} == 3'b100);
  cover property (@(IN1 or IN2 or IN3)
                  pwr_good && in_known && {IN1,IN2,IN3} == 3'b101);
  cover property (@(IN1 or IN2 or IN3)
                  pwr_good && in_known && {IN1,IN2,IN3} == 3'b110);
  cover property (@(IN1 or IN2 or IN3)
                  pwr_good && in_known && {IN1,IN2,IN3} == 3'b111);

  // - Observe both output values under good power
  cover property (@(IN1 or IN2 or IN3 or VDD or VSS)
                  pwr_good && in_known && (QN === 1'b0));
  cover property (@(IN1 or IN2 or IN3 or VDD or VSS)
                  pwr_good && in_known && (QN === 1'b1));

  // - Power states hit
  cover property (@(VDD or VSS) (pwr_good));
  cover property (@(VDD or VSS) (!pwr_good));

endmodule