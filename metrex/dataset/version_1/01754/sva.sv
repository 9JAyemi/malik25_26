// SVA for counter_mod_rtl
module counter_mod_sva(
  input clk, rst, up_down,
  input [3:0] q,
  input carry
);

  // Track when $past() is valid (post-reset)
  logic past_valid;
  always @(posedge clk or posedge rst) begin
    if (rst) past_valid <= 1'b0;
    else     past_valid <= 1'b1;
  end

  // Reset drives outputs to zero whenever asserted
  assert property (@(posedge clk) rst |-> (q==4'h0 && carry==1'b0));

  // No X/Z on key signals once out of reset
  assert property (@(posedge clk) (!rst && past_valid) |-> !$isunknown({q, carry, up_down}));

  // Up: normal increment (no wrap) with carry deasserted
  assert property (@(posedge clk)
    (past_valid && !rst && $past(up_down)==1'b0 && $past(q)!=4'hF)
    |-> (q==$past(q)+4'h1 && carry==1'b0));

  // Up: wrap with carry
  assert property (@(posedge clk)
    (past_valid && !rst && $past(up_down)==1'b0 && $past(q)==4'hF)
    |-> (q==4'h0 && carry==1'b1));

  // Down: normal decrement (no wrap) with carry deasserted
  assert property (@(posedge clk)
    (past_valid && !rst && $past(up_down)==1'b1 && $past(q)!=4'h0)
    |-> (q==$past(q)-4'h1 && carry==1'b0));

  // Down: wrap with carry
  assert property (@(posedge clk)
    (past_valid && !rst && $past(up_down)==1'b1 && $past(q)==4'h0)
    |-> (q==4'hF && carry==1'b1));

  // Carry only on wrap, and carry is a 1-cycle pulse
  assert property (@(posedge clk)
    (past_valid && !rst && carry)
    |-> (($past(up_down)==1'b0 && $past(q)==4'hF) ||
         ($past(up_down)==1'b1 && $past(q)==4'h0)));
  assert property (@(posedge clk) (past_valid && !rst && carry) |=> !carry);

  // Functional coverage
  cover property (@(posedge clk) $rose(rst));
  cover property (@(posedge clk) past_valid && !rst && $past(up_down)==1'b0 && $past(q)==4'hF && q==4'h0 && carry); // up wrap
  cover property (@(posedge clk) past_valid && !rst && $past(up_down)==1'b1 && $past(q)==4'h0 && q==4'hF && carry); // down wrap
  cover property (@(posedge clk) past_valid && !rst && $past(up_down)==1'b0 && $past(q)!=4'hF && q==$past(q)+4'h1 && !carry); // up step
  cover property (@(posedge clk) past_valid && !rst && $past(up_down)==1'b1 && $past(q)!=4'h0 && q==$past(q)-4'h1 && !carry); // down step
  cover property (@(posedge clk) past_valid && !rst && $past(up_down)==1'b0 && up_down==1'b1); // change up->down
  cover property (@(posedge clk) past_valid && !rst && $past(up_down)==1'b1 && up_down==1'b0); // change down->up

endmodule

// Bind into the DUT
bind counter_mod_rtl counter_mod_sva svac(
  .clk(clk), .rst(rst), .up_down(up_down), .q(q), .carry(carry)
);