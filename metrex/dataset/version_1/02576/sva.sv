// SVA for sparc_ifu_cmp35
module sparc_ifu_cmp35_sva (
  input logic [34:0] a, b,
  input logic        valid,
  input logic        hit
);

  // Functional correctness (same-cycle, combinational)
  assert property (@(a or b or valid)
                   (valid && !$isunknown({a,b}) && (a == b)) |-> (hit == 1'b1))
    else $error("cmp35: hit must be 1 when valid and a==b");

  assert property (@(a or b or valid)
                   (valid && !$isunknown({a,b}) && (a != b)) |-> (hit == 1'b0))
    else $error("cmp35: hit must be 0 when valid and a!=b");

  // If any input bit is X/Z under valid, DUT drives 0 (if-condition is not 1)
  assert property (@(a or b or valid)
                   (valid && $isunknown({a,b})) |-> (hit == 1'b0))
    else $error("cmp35: hit must be 0 when inputs unknown and valid");

  // Not valid => hit must be 0
  assert property (@(a or b or valid)
                   (!valid) |-> (hit == 1'b0))
    else $error("cmp35: hit must be 0 when not valid");

  // Sanity: hit never X/Z and hit implies valid and known equal
  assert property (@(a or b or valid) !$isunknown(hit))
    else $error("cmp35: hit is X/Z");

  assert property (@(a or b or valid)
                   hit |-> (valid && !$isunknown({a,b}) && (a == b)))
    else $error("cmp35: hit implies valid and a==b");

  // Coverage
  cover property (@(a or b or valid)
                  (valid && !$isunknown({a,b}) && (a == b) && hit));
  cover property (@(a or b or valid)
                  (valid && !$isunknown({a,b}) && (a != b) && !hit));
  cover property (@(a or b or valid)
                  (!valid && !hit));
  cover property (@(a or b or valid)
                  (!hit) ##1 hit ##1 !hit); // observe 0->1->0 toggle

endmodule

bind sparc_ifu_cmp35 sparc_ifu_cmp35_sva i_cmp35_sva(.a(a), .b(b), .valid(valid), .hit(hit));