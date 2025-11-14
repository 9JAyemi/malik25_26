// SVA checkers and binds for the provided design

module b2oh_sva (input [2:0] B, input [7:0] Y);
  // Combinational correctness
  always_comb begin
    assert ($onehot(Y)) else $error("binary_to_onehot: Y not one-hot (B=%0d Y=%b)", B, Y);
    assert (Y == (8'h1 << B)) else $error("binary_to_onehot: Y != (1<<B) (B=%0d Y=%b)", B, Y);
  end
endmodule


module udc_sva (input clk, reset, Up, Down, Load, input [7:0] D, input [7:0] Q);
  bit past_valid;
  always @(posedge clk) past_valid <= 1'b1;

  default clocking cb @(posedge clk); endclocking

  // Reset clears Q
  assert property (past_valid && $past(reset) |-> (Q == 8'h00));

  // Load has priority over Up/Down
  assert property (past_valid && !reset && Load |=> (Q == $past(D)));

  // Up increments (priority over Down)
  assert property (past_valid && !reset && !Load && Up |=> (Q == $past(Q) + 8'd1));

  // Down decrements only when Up==0
  assert property (past_valid && !reset && !Load && !Up && Down |=> (Q == $past(Q) - 8'd1));

  // Hold when no control asserted
  assert property (past_valid && !reset && !Load && !Up && !Down |=> (Q == $past(Q)));

  // Simultaneous Up&Down => Up wins
  assert property (past_valid && !reset && !Load && Up && Down |=> (Q == $past(Q) + 8'd1));

  // Coverage
  cover property (past_valid && !reset && Load);
  cover property (past_valid && !reset && !Load && Up && !Down);
  cover property (past_valid && !reset && !Load && Down && !Up);
  cover property (past_valid && !reset && !Load && Up && Down);
  cover property (past_valid && !reset && !Load && Up && ($past(Q)==8'hFF) |=> (Q==8'h00)); // wrap up
  cover property (past_valid && !reset && !Load && !Up && Down && ($past(Q)==8'h00) |=> (Q==8'hFF)); // wrap down
endmodule


module ohc_sva (input clk, reset, input [2:0] B,
                input Up, Down, Load,
                input [7:0] onehot, input [7:0] next_onehot, input [7:0] Q);
  bit past_valid;
  always @(posedge clk) past_valid <= 1'b1;

  default clocking cb @(posedge clk); endclocking

  // One-hot converter correctness as seen in this scope
  assert property ($onehot(onehot));
  assert property (onehot == (8'h1 << B));

  // Pipeline: Q follows next_onehot by 1 cycle; reset clears Q
  assert property (past_valid && $past(reset) |-> (Q == 8'h00));
  assert property (past_valid && !reset |-> (Q == $past(next_onehot)));

  // Cover all B encodings reaching corresponding onehot
  genvar i;
  generate
    for (i=0; i<8; i++) begin : covB
      cover property (!reset && (B == i) && (onehot == (8'h1 << i)));
    end
  endgenerate

  // Observe handoff from next_onehot to Q
  cover property (past_valid && !reset && $changed(next_onehot) |-> ##1 $changed(Q));
endmodule


// Bind checkers
bind binary_to_onehot b2oh_sva b2oh_sva_i (.*);
bind up_down_counter  udc_sva  udc_sva_i  (.*);
bind one_hot_counter  ohc_sva  ohc_sva_i  (.*);