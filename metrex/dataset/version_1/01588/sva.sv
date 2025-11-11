// SVA for nor3 and nor4 (bind into DUTs). Focused, full functional checks and input-space coverage.

module nor3_sva;
  // Functional correctness (4-state exact)
  a_func: assert property (@(*) (Y === ~(A | B | C)))
    else $error("nor3: Y != ~(A|B|C)");

  // Input-space coverage (all 8 combos) with expected Y
  cover property (@(*) ({A,B,C} === 3'b000 && Y === 1'b1));
  cover property (@(*) ({A,B,C} === 3'b001 && Y === 1'b0));
  cover property (@(*) ({A,B,C} === 3'b010 && Y === 1'b0));
  cover property (@(*) ({A,B,C} === 3'b011 && Y === 1'b0));
  cover property (@(*) ({A,B,C} === 3'b100 && Y === 1'b0));
  cover property (@(*) ({A,B,C} === 3'b101 && Y === 1'b0));
  cover property (@(*) ({A,B,C} === 3'b110 && Y === 1'b0));
  cover property (@(*) ({A,B,C} === 3'b111 && Y === 1'b0));
endmodule

bind nor3 nor3_sva nor3_sva_i();


module nor4_sva;
  // Internal structure checks (catch miswires)
  a_n1: assert property (@(*) (n1 === ~(A | B | C))) else $error("nor4.n1 mismatch");
  a_n2: assert property (@(*) (n2 === ~(B | C | D))) else $error("nor4.n2 mismatch");
  a_n3: assert property (@(*) (n3 === ~(A | C | D))) else $error("nor4.n3 mismatch");
  a_n4: assert property (@(*) (n4 === ~(A | B | D))) else $error("nor4.n4 mismatch");
  a_n5: assert property (@(*) (n5 === ~(n1 | n2 | n3))) else $error("nor4.n5 mismatch");
  a_out_path: assert property (@(*) (Y  === ~(n5 | n4 | D))) else $error("nor4.Y path mismatch");

  // Overall functional equivalence to a 4-input NOR (4-state exact)
  a_func_equiv: assert property (@(*) (Y === ~(A | B | C | D)))
    else $error("nor4: Y != ~(A|B|C|D)");

  // Input-space coverage (all 16 combos) with expected Y
  cover property (@(*) ({A,B,C,D} === 4'b0000 && Y === 1'b1));
  cover property (@(*) ({A,B,C,D} === 4'b0001 && Y === 1'b0));
  cover property (@(*) ({A,B,C,D} === 4'b0010 && Y === 1'b0));
  cover property (@(*) ({A,B,C,D} === 4'b0011 && Y === 1'b0));
  cover property (@(*) ({A,B,C,D} === 4'b0100 && Y === 1'b0));
  cover property (@(*) ({A,B,C,D} === 4'b0101 && Y === 1'b0));
  cover property (@(*) ({A,B,C,D} === 4'b0110 && Y === 1'b0));
  cover property (@(*) ({A,B,C,D} === 4'b0111 && Y === 1'b0));
  cover property (@(*) ({A,B,C,D} === 4'b1000 && Y === 1'b0));
  cover property (@(*) ({A,B,C,D} === 4'b1001 && Y === 1'b0));
  cover property (@(*) ({A,B,C,D} === 4'b1010 && Y === 1'b0));
  cover property (@(*) ({A,B,C,D} === 4'b1011 && Y === 1'b0));
  cover property (@(*) ({A,B,C,D} === 4'b1100 && Y === 1'b0));
  cover property (@(*) ({A,B,C,D} === 4'b1101 && Y === 1'b0));
  cover property (@(*) ({A,B,C,D} === 4'b1110 && Y === 1'b0));
  cover property (@(*) ({A,B,C,D} === 4'b1111 && Y === 1'b0));
endmodule

bind nor4 nor4_sva nor4_sva_i();