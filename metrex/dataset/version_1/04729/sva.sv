// SVA for oneshot_2clk
// Bind into the DUT to access internals
bind oneshot_2clk oneshot_2clk_assert u_oneshot_2clk_assert (
  .clk_in(clk_in),
  .clk_out(clk_out),
  .in(in),
  .out(out),
  .del_in(del_in),
  .sendit(sendit),
  .sendit_d(sendit_d),
  .gotit_d(gotit_d),
  .gotit(gotit)
);

module oneshot_2clk_assert (
  input logic clk_in, clk_out,
  input logic in, out,
  input logic del_in, sendit, sendit_d, gotit_d, gotit
);

  // Disable all assertions at init to avoid $past startup Xs
  default disable iff ($initstate);

  // Basic flop wiring checks
  assert property (@(posedge clk_in)  del_in   == $past(in));
  assert property (@(posedge clk_out) sendit_d == $past(sendit));
  assert property (@(posedge clk_out) out      == $past(sendit_d));
  assert property (@(posedge clk_in)  gotit_d  == $past(out));
  assert property (@(posedge clk_in)  gotit    == $past(gotit_d));

  // Edge detect correctness
  assert property (@(posedge clk_in) (in & ~del_in) <-> $rose(in));

  // sendit protocol
  // sendit can only rise due to a detected input edge
  assert property (@(posedge clk_in) $rose(sendit) |-> $past(in & ~del_in));
  // Once raised, sendit holds until gotit is seen
  assert property (@(posedge clk_in) $rose(sendit) |-> sendit until_with gotit);
  // If gotit and no new edge this cycle, clear on next cycle
  assert property (@(posedge clk_in) gotit && !(in & ~del_in) |=> !sendit);
  // A fall of sendit only happens due to gotit without a concurrent set
  assert property (@(posedge clk_in) $fell(sendit) |-> $past(gotit && !(in & ~del_in)));
  // If gotit coincides with a new input edge, sendit stays asserted
  assert property (@(posedge clk_in) gotit && (in & ~del_in) |=> sendit);

  // Cross-clock liveness (eventually properties)
  // An input edge eventually makes out asserted in clk_out domain
  assert property (@(posedge clk_in)  $rose(in)
                   |-> ##[0:$] @(posedge clk_out) out);
  // Once out is seen, gotit will eventually be seen back in clk_in domain
  assert property (@(posedge clk_out) out
                   |-> ##[0:$] @(posedge clk_in) gotit);
  // After gotit, out eventually deasserts
  assert property (@(posedge clk_in)  gotit
                   |-> ##[1:$] @(posedge clk_out) !out);

  // out minimum width (at least one full clk_out cycle when it rises)
  assert property (@(posedge clk_out) $rose(out) |=> out);

  // Coverage
  // Full handshake: in edge -> out rises -> gotit -> out falls
  cover property (@(posedge clk_in)  $rose(in)
                  ##[1:$] @(posedge clk_out) $rose(out)
                  ##[1:$] @(posedge clk_in)  $rose(gotit)
                  ##[1:$] @(posedge clk_out) $fell(out));

  // Back-to-back input edges while previous transfer is in-flight
  cover property (@(posedge clk_in) $rose(in)
                  ##[1:$] (sendit && $rose(in)));

  // Case where out is stretched for multiple clk_out cycles
  cover property (@(posedge clk_out) out[*3]);

endmodule