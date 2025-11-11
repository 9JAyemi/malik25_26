// SVA checker for comparator_block
// Bind this to the DUT and provide a sampling clock/reset.
// Example:
//   bind comparator_block comparator_block_sva #(.n(n)) u_chk (.* , .clk(clk), .rst_n(rst_n));

module comparator_block_sva #(parameter int n = 4)
(
  input logic                  clk,
  input logic                  rst_n,
  input logic [n-1:0]          A,
  input logic [n-1:0]          B,
  input logic [1:0]            eq_gt
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n)

  // Shorthands
  localparam logic [n-1:0] ALLX = {n{1'bx}};
  function automatic bit allx(input logic [n-1:0] v); return (v === ALLX); endfunction

  // Core correctness: mirror the intended spec (4-state semantics and else-if priority)
  // Piecewise properties matching the DUT decision tree
  // 1) Equal (4-state) -> 11
  assert property ( (A === B) |-> (eq_gt == 2'b11) );

  // 2) Greater -> 10
  assert property ( (A > B)  |-> (eq_gt == 2'b10) );

  // 3) Less -> 01
  assert property ( (A < B)  |-> (eq_gt == 2'b01) );

  // 4) A is all X, B is not all X -> 01
  assert property ( allx(A) && !allx(B) |-> (eq_gt == 2'b01) );

  // 5) A is not all X, B is all X -> 10
  assert property ( !allx(A) && allx(B) |-> (eq_gt == 2'b10) );

  // 6) Else clause: none of the above -> 10
  assert property (
    !(A === B) &&
    !(A > B)  &&
    !(A < B)  &&
    !(allx(A) && !allx(B)) &&
    !(!allx(A) && allx(B))
    |-> (eq_gt == 2'b10)
  );

  // Output integrity
  // Never 00; no X/Z on output; stable outputs when inputs are stable
  assert property ( eq_gt inside {2'b01,2'b10,2'b11} );
  assert property ( !$isunknown(eq_gt) );
  assert property ( $stable(A) && $stable(B) |-> $stable(eq_gt) );

  // Functional covers (hit each intended behavior, including X-cases)
  cover property ( (A === B) && !$isunknown({A,B}) && (eq_gt == 2'b11) ); // equal, known
  cover property ( (A >  B) && !$isunknown({A,B}) && (eq_gt == 2'b10) ); // greater, known
  cover property ( (A <  B) && !$isunknown({A,B}) && (eq_gt == 2'b01) ); // less, known
  cover property ( (A === B) &&  $isunknown({A,B}) && (eq_gt == 2'b11) ); // equal with X pattern
  cover property ( allx(A) && !allx(B) && (eq_gt == 2'b01) ); // A all X, B not
  cover property ( !allx(A) && allx(B) && (eq_gt == 2'b10) ); // B all X, A not
  // Else-path: both have Xs (not all-X), not equal in 4-state, rel ops unknown -> 10
  cover property (
    $isunknown(A) && $isunknown(B) &&
    !allx(A) && !allx(B) &&
    !(A === B) && !(A > B) && !(A < B) &&
    (eq_gt == 2'b10)
  );

endmodule