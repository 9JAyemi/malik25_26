// SVA for planeB. Bind this to the DUT instance.
// Example: bind planeB planeB_sva #(.pL(pL), .pW(pW), .wL(wL), .wW(wW), .wP(wP)) planeB_sva_i (.*);

module planeB_sva #(
  parameter int pL = 40,
  parameter int pW = 10,
  parameter int wL = 15,
  parameter int wW = 15,
  parameter int wP = 10
)(
  input logic        clk,
  input logic        rst,
  input logic [10:0] x,
  input logic [10:0] y,
  input logic [10:0] poX,
  input logic [10:0] poY,
  input logic        wing,
  input logic        body
);

  default clocking cb @(posedge clk); endclocking

  // Geometric predicates (match DUT operator precedence and strict inequalities)
  let body_c  = (x < poX+pL) && (x > poX) &&
                (y < poY+wL+pW) && (y > poY+wL);

  let wing1_c = (x < poX+wP+wW) && (x > poX+wP) &&
                (y < poY+wL)    && (y > poY) &&
                ((x-poX)+(y-poY) > (wW+wP));

  let wing2_c = (x < poX+wP+wW) && (x > poX+wP) &&
                (y > poY+wL+pW) && (y < poY+(wL+wL)+pW) &&
                ((x-poX)-(y-poY) > (wP-wL-pW));

  let wing_c  = wing1_c || wing2_c;

  // Reset behavior (async and sync)
  a_reset_sync:  assert property (rst |-> (!body && !wing));
  a_reset_async: assert property (@(posedge rst) 1'b1 |-> (!body && !wing));

  // Functional correctness
  a_body_func: assert property (disable iff (rst) body == body_c);
  a_wing_func: assert property (disable iff (rst) wing == wing_c);

  // Mutual exclusion
  a_mutex: assert property (disable iff (rst) !(body && wing));

  // Stability when inputs stable
  a_stable: assert property (disable iff (rst) $stable({x,y,poX,poY}) |-> $stable({body,wing}));

  // No X/Z on critical signals at sample
  a_nox: assert property (!$isunknown({x,y,poX,poY,rst,body,wing}));

  // Boundary checks: equality at any strict edge must yield 0
  a_body_edges_zero: assert property (disable iff (rst)
    ((x==poX) || (x==poX+pL) || (y==poY+wL) || (y==poY+wL+pW)) |-> (body==1'b0));

  a_wing1_edges_zero: assert property (disable iff (rst)
    ((x==poX+wP) || (x==poX+wP+wW) || (y==poY) || (y==poY+wL) ||
     (((x-poX)+(y-poY)) == (wW+wP))) |-> (wing==1'b0));

  a_wing2_edges_zero: assert property (disable iff (rst)
    ((y==poY+wL+pW) || (y==poY+(wL+wL)+pW) ||
     (((x-poX)-(y-poY)) == (wP-wL-pW))) |-> (wing==1'b0));

  // Basic functional coverage
  c_body_on:  cover property (disable iff (rst) body_c  && body);
  c_w1_on:    cover property (disable iff (rst) wing1_c && wing);
  c_w2_on:    cover property (disable iff (rst) wing2_c && wing);
  c_none_on:  cover property (disable iff (rst) !(body || wing));

  // Edge-touch coverage
  c_body_edge: cover property (disable iff (rst)
    (x==poX || x==poX+pL || y==poY+wL || y==poY+wL+pW) && (body==0));

  c_wing_edges: cover property (disable iff (rst)
    ((x==poX+wP) || (x==poX+wP+wW) || (y==poY) || (y==poY+wL) ||
     ((x-poX)+(y-poY)==(wW+wP)) ||
     (y==poY+wL+pW) || (y==poY+(wL+wL)+pW) ||
     ((x-poX)-(y-poY)==(wP-wL-pW))) && (wing==0));

endmodule