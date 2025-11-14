// SVA checker for nor4
module nor4_sva (
  input logic A, B, C, D,
  input logic Y,
  input logic temp1, temp2
);

  // Sample on any input edge
  default clocking cb @(
    posedge A or negedge A or
    posedge B or negedge B or
    posedge C or negedge C or
    posedge D or negedge D
  ); endclocking

  // Spec: true 4-input NOR (this will flag the current DUT bug)
  assert property (Y === ~(|{A,B,C,D})))
    else $error("nor4 spec mismatch: Y != ~(A|B|C|D)");

  // Structural checks for the three NOR gates
  assert property (temp1 === ~(|{A,B})))
    else $error("nor1 mismatch: temp1 != ~(A|B)");
  assert property (temp2 === ~(|{C,D})))
    else $error("nor2 mismatch: temp2 != ~(C|D)");
  assert property (Y === ~(|{temp1,temp2})))
    else $error("nor3 mismatch: Y != ~(temp1|temp2)");

  // No X/Z on temps/output when all inputs are known
  assert property ((!$isunknown({A,B,C,D})) |-> (!$isunknown(temp1) && !$isunknown(temp2) && !$isunknown(Y))))
    else $error("Unknown detected on outputs with known inputs");

  // Minimal but complete coverage
  cover property (Y == 1'b1);
  cover property (Y == 1'b0);
  cover property ($rose(Y));
  cover property ($fell(Y));

  genvar i;
  generate
    for (i = 0; i < 16; i++) begin : CMB
      cover property ({A,B,C,D} == i[3:0]);
    end
  endgenerate

endmodule

// Bind into DUT (accesses internal temp1/temp2)
bind nor4 nor4_sva nor4_sva_i (.A(A), .B(B), .C(C), .D(D), .Y(Y), .temp1(temp1), .temp2(temp2));