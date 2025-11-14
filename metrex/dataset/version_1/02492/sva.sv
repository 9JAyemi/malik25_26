// SVA for airplane — concise, quality-focused
// Bindable checker that verifies functional equivalence, reset behavior, X-prop, and covers key regions.

module airplane_sva #(parameter int pL=40, pW=10, wL=15, wW=15, wP=15)
(
  input  logic        clk,
  input  logic        rst,
  input  logic [10:0] x,
  input  logic [10:0] y,
  input  logic [10:0] poX,
  input  logic [10:0] poY,
  input  logic        wing,
  input  logic        body
);

  default clocking cb @(posedge clk); endclocking

  // Geometry/logic as in RTL
  let body_c  = (x < poX+pL) && (x > poX) &&
                (y < poY+wL+pW) && (y > poY+wL);

  let wing_c1 = (x < poX+wP+wW) && (x > poX+wP) &&
                (y < poY+wL)    && (y > poY) &&
                (x - y - poX + poY < wP);

  let wing_c2 = (x < poX+wP+wW) && (x > poX+wP) &&
                (y > poY+wL+pW) && (y < poY+wL+wL+pW) &&
                (x - poX + y - poY < wP + pL);

  // Async reset drives outputs low immediately (use ##0 to observe post-NBA)
  assert property (@(posedge rst) 1'b1 |-> ##0 (wing==1'b0 && body==1'b0))
    else $error("airplane: outputs not 0 on async reset");

  // While rst=1 at a clock edge, outputs are 0 after that edge
  assert property (@(posedge clk) rst |-> ##0 (wing==1'b0 && body==1'b0))
    else $error("airplane: outputs not 0 while rst=1");

  // Functional equivalence (sample outputs after NBA via ##0)
  assert property (disable iff (rst) 1'b1 |-> ##0 (body == body_c))
    else $error("airplane: body mismatch");

  assert property (disable iff (rst) 1'b1 |-> ##0 (wing == (wing_c1 || wing_c2)))
    else $error("airplane: wing mismatch");

  // No X/Z on outputs in active operation
  assert property (disable iff (rst) 1'b1 |-> ##0 (!$isunknown({wing,body})))
    else $error("airplane: X/Z on outputs");

  // By construction, body and wing regions do not overlap in y; they must not be 1 together
  assert property (disable iff (rst) !(wing && body))
    else $error("airplane: wing and body both 1");

  // Coverage: reset, each wing branch, body region, edges/toggles
  cover property (@(posedge rst) ##0 (wing==0 && body==0));
  cover property (disable iff (rst) body_c ##0 body);
  cover property (disable iff (rst) wing_c1 && !wing_c2 ##0 wing);
  cover property (disable iff (rst) wing_c2 && !wing_c1 ##0 wing);
  cover property (disable iff (rst) !wing_c1 && !wing_c2 ##0 !wing);
  cover property (disable iff (rst) $rose(wing));
  cover property (disable iff (rst) $fell(wing));
  cover property (disable iff (rst) $rose(body));
  cover property (disable iff (rst) $fell(body));

endmodule

// Bind to the DUT
bind airplane airplane_sva #(.pL(pL), .pW(pW), .wL(wL), .wW(wW), .wP(wP)) airplane_sva_i
(
  .clk(clk), .rst(rst), .x(x), .y(y), .poX(poX), .poY(poY), .wing(wing), .body(body)
);