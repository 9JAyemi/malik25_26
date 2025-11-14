// SVA for alu_flags
module alu_flags_sva
(
  input logic [/*auto*/] srcA,
  input logic [/*auto*/] srcB,
  input logic [3:0]      aluop,
  input logic            zero,
  input logic            of,
  input logic            uof
);
  // Use port widths
  localparam int DW = $bits(srcA);

  default clocking cb @(*); endclocking

  // Helpers
  let add_op    = (aluop == 4'd5);
  let sub_op    = (aluop == 4'd6);
  let add_full  = {1'b0, srcA} + {1'b0, srcB};
  let sub_full  = {1'b0, srcA} - {1'b0, srcB};
  let add_carry = add_full[DW];
  let sub_carry = sub_full[DW];
  let add_msb   = add_full[DW-1];
  let sub_msb   = sub_full[DW-1];
  let sA        = srcA[DW-1];
  let sB        = srcB[DW-1];

  let exp_zero  = (srcA == srcB);
  let exp_of    = add_op ? ((sA & sB & ~add_msb) | (~sA & ~sB & add_msb))
                         : sub_op ? ((sA & ~sB & ~sub_msb) | (~sA &  sB &  sub_msb))
                                  : 1'b0;
  let exp_uof   = add_op ? add_carry
                         : sub_op ? sub_carry
                                  : 1'b0;

  // Functional checks
  assert property (zero == exp_zero);
  assert property (of   == exp_of);
  assert property (uof  == exp_uof);

  // For non-add/sub ops, flags must be 0
  assert property ((!add_op && !sub_op) |-> (of == 1'b0 && uof == 1'b0));

  // No X/Z on outputs when inputs known
  assert property (!$isunknown({srcA, srcB, aluop}) |-> !$isunknown({zero, of, uof}));

  // Corner/overflow coverage
  cover property (add_op && (sA == 1'b0) && (sB == 1'b0) && (add_msb == 1'b1) && of); // + + -> overflow
  cover property (add_op && (sA == 1'b1) && (sB == 1'b1) && (add_msb == 1'b0) && of); // - - -> overflow
  cover property (sub_op && (sA == 1'b1) && (sB == 1'b0) && (sub_msb == 1'b0) && of); // - - + -> overflow
  cover property (sub_op && (sA == 1'b0) && (sB == 1'b1) && (sub_msb == 1'b1) && of); // + - -> - overflow
  cover property (add_op && add_carry && uof);             // unsigned add overflow
  cover property (sub_op && sub_carry && uof);             // unsigned sub "no borrow" per DUT
  cover property (sub_op && !sub_carry && !uof);           // borrow case observed
  cover property (zero);                                    // equality detected
  cover property (!zero);                                   // inequality detected
  cover property (!add_op && !sub_op && (of == 1'b0) && (uof == 1'b0)); // other ALU ops
endmodule

// Bind into DUT
bind alu_flags alu_flags_sva i_alu_flags_sva (.*);