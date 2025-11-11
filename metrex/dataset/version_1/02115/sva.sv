// SVA for NOR4X0
// Checks structure, function, X-robustness (when inputs known), and covers all input combos.

bind NOR4X0 NOR4X0_sva i_NOR4X0_sva (.*);

module NOR4X0_sva
(
  input  logic IN1, IN2, IN3, IN4,
  input  logic n1, n2, n3, n4,
  input  logic QN
);

  // Sample on any change to inputs or output
  default clocking cb @ (IN1 or IN2 or IN3 or IN4 or QN or n1 or n2 or n3 or n4); endclocking

  // Structural checks (4-state, match NAND chain)
  assert property (n1 === ~(IN1 & IN2)) else $error("NOR4X0: n1 mismatch");
  assert property (n2 === ~(IN3 & IN4)) else $error("NOR4X0: n2 mismatch");
  assert property (n3 === ~(n1 & n2))   else $error("NOR4X0: n3 mismatch");
  assert property (n4 === ~n3)           else $error("NOR4X0: n4 mismatch");
  assert property (QN === ~n4)           else $error("NOR4X0: QN!=~n4");

  // Functional check (when evaluating in same timestep after input change)
  // QN must equal (IN1&IN2)|(IN3&IN4)
  property p_func;
    $changed({IN1,IN2,IN3,IN4}) |-> ##0 (QN === ((IN1 & IN2) | (IN3 & IN4)));
  endproperty
  assert property (p_func) else
    $error("NOR4X0: func mismatch QN=%0b IN={%0b%0b%0b%0b}", QN, IN1,IN2,IN3,IN4);

  // Knownness: if all inputs are known, output must be known
  assert property ( (!$isunknown({IN1,IN2,IN3,IN4})) |-> ##0 (!$isunknown(QN)) )
    else $error("NOR4X0: QN unknown with known inputs");

  // Output toggle coverage
  cover property ($rose(QN));
  cover property ($fell(QN));

  // Full input-space coverage (only 0/1, exclude X/Z)
  cover property (! $isunknown({IN1,IN2,IN3,IN4}) && {IN1,IN2,IN3,IN4} == 4'b0000);
  cover property (! $isunknown({IN1,IN2,IN3,IN4}) && {IN1,IN2,IN3,IN4} == 4'b0001);
  cover property (! $isunknown({IN1,IN2,IN3,IN4}) && {IN1,IN2,IN3,IN4} == 4'b0010);
  cover property (! $isunknown({IN1,IN2,IN3,IN4}) && {IN1,IN2,IN3,IN4} == 4'b0011);
  cover property (! $isunknown({IN1,IN2,IN3,IN4}) && {IN1,IN2,IN3,IN4} == 4'b0100);
  cover property (! $isunknown({IN1,IN2,IN3,IN4}) && {IN1,IN2,IN3,IN4} == 4'b0101);
  cover property (! $isunknown({IN1,IN2,IN3,IN4}) && {IN1,IN2,IN3,IN4} == 4'b0110);
  cover property (! $isunknown({IN1,IN2,IN3,IN4}) && {IN1,IN2,IN3,IN4} == 4'b0111);
  cover property (! $isunknown({IN1,IN2,IN3,IN4}) && {IN1,IN2,IN3,IN4} == 4'b1000);
  cover property (! $isunknown({IN1,IN2,IN3,IN4}) && {IN1,IN2,IN3,IN4} == 4'b1001);
  cover property (! $isunknown({IN1,IN2,IN3,IN4}) && {IN1,IN2,IN3,IN4} == 4'b1010);
  cover property (! $isunknown({IN1,IN2,IN3,IN4}) && {IN1,IN2,IN3,IN4} == 4'b1011);
  cover property (! $isunknown({IN1,IN2,IN3,IN4}) && {IN1,IN2,IN3,IN4} == 4'b1100);
  cover property (! $isunknown({IN1,IN2,IN3,IN4}) && {IN1,IN2,IN3,IN4} == 4'b1101);
  cover property (! $isunknown({IN1,IN2,IN3,IN4}) && {IN1,IN2,IN3,IN4} == 4'b1110);
  cover property (! $isunknown({IN1,IN2,IN3,IN4}) && {IN1,IN2,IN3,IN4} == 4'b1111);

endmodule