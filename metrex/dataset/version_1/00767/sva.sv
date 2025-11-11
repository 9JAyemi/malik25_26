// SVA for updown_counter
// Concise checks of pipeline staging, functional update, wrap-around, and coverage.

`default_nettype none

module updown_counter_sva (
  input  logic       clk,
  input  logic       U_D,
  input  logic [3:0] Q,
  input  logic [3:0] Q_reg1,
  input  logic [3:0] Q_reg2
);

  // Warm-up for $past
  logic past1, past2, past3;
  always_ff @(posedge clk) begin
    past1 <= 1'b1;
    past2 <= past1;
    past3 <= past2;
  end

  // Control must be known after warm-up
  assert property (@(posedge clk) disable iff (!past1)
                   !$isunknown(U_D))
    else $error("U_D is X/Z");

  // Pipeline staging
  assert property (@(posedge clk) disable iff (!past1)
                   Q_reg1 == $past(Q));
  assert property (@(posedge clk) disable iff (!past1)
                   Q_reg2 == $past(Q_reg1));
  assert property (@(posedge clk) disable iff (!past2)
                   Q_reg2 == $past(Q,2));

  // Functional update (uses previous-cycle U_D and Q_reg2)
  assert property (@(posedge clk) disable iff (!past1)
                   Q == ( $past(U_D) ? ($past(Q_reg2)+4'd1) : ($past(Q_reg2)-4'd1) ));

  // Direct 3-cycle relation on Q (redundant but strong)
  assert property (@(posedge clk) disable iff (!past3)
                   Q == ( $past(U_D,1) ? ($past(Q,3)+4'd1) : ($past(Q,3)-4'd1) ));

  // Explicit wrap-around checks
  assert property (@(posedge clk) disable iff (!past1)
                   ($past(U_D) && ($past(Q_reg2)==4'hF)) |-> (Q==4'h0));
  assert property (@(posedge clk) disable iff (!past1)
                   ((!$past(U_D)) && ($past(Q_reg2)==4'h0)) |-> (Q==4'hF));

  // Coverage
  cover property (@(posedge clk) disable iff (!past1)
                  $past(U_D) && (Q == $past(Q_reg2)+4'd1));
  cover property (@(posedge clk) disable iff (!past1)
                  !$past(U_D) && (Q == $past(Q_reg2)-4'd1));
  cover property (@(posedge clk) disable iff (!past1)
                  $past(U_D) && ($past(Q_reg2)==4'hF) && (Q==4'h0));
  cover property (@(posedge clk) disable iff (!past1)
                  !$past(U_D) && ($past(Q_reg2)==4'h0) && (Q==4'hF));
  cover property (@(posedge clk) disable iff (!past2)
                  ($past(U_D,2)==1) && ($past(U_D,1)==0)); // up->down
  cover property (@(posedge clk) disable iff (!past2)
                  ($past(U_D,2)==0) && ($past(U_D,1)==1)); // down->up

endmodule

// Bind into DUT (ports use DUT internal names)
bind updown_counter updown_counter_sva sva (.clk(clk), .U_D(U_D), .Q(Q), .Q_reg1(Q_reg1), .Q_reg2(Q_reg2));

`default_nettype wire