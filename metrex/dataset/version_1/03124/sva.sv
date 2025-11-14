// SVA for debounce_switch
// Bind this file to the DUT
bind debounce_switch debounce_switch_sva #(.WIDTH(WIDTH), .N(N), .RATE(RATE)) u_debounce_switch_sva();

module debounce_switch_sva #(parameter int WIDTH=1, N=3, RATE=125000) ();

  // Access DUT scope directly (bind-scope)
  // clk, rst, in, out, cnt_reg, debounce_reg, state

  // Parameter guards
  initial begin
    assert (N >= 2) else $fatal(1,"debounce_switch: N (%0d) must be >= 2", N);
    assert (RATE <= 24'hFFFFFF) else $fatal(1,"debounce_switch: RATE (%0d) must fit in 24 bits", RATE);
  end

  default clocking cb @(posedge clk); endclocking
  // Properties below are disabled while in reset
  default disable iff (rst);

  // Combinational connectivity
  assert property (out == state);

  // Reset behavior (level)
  assert property (@(posedge clk) rst |-> (cnt_reg == 24'd0 && state == {WIDTH{1'b0}}));
  genvar r;
  generate
    for (r=0; r<WIDTH; r++) begin : G_RST
      assert property (@(posedge clk) rst |-> debounce_reg[r] == {N{1'b0}});
    end
  endgenerate

  // Counter next-state semantics
  assert property ((cnt_reg < RATE) |=> cnt_reg == $past(cnt_reg) + 24'd1);
  assert property ((cnt_reg >= RATE) |=> cnt_reg == 24'd0);

  // Debounce shift-register update
  generate if (N >= 2) begin : G_SHIFT
    genvar i;
    for (i=0; i<WIDTH; i++) begin : G_SR
      // Shift only when cnt_reg==0
      assert property ((cnt_reg == 24'd0) |=> debounce_reg[i] == { $past(debounce_reg[i][N-2:0]), $past(in[i]) });
      // Hold otherwise
      assert property ((cnt_reg != 24'd0) |=> debounce_reg[i] == $past(debounce_reg[i]));
    end
  end else begin
    initial $fatal(1,"debounce_switch: N must be >=2 for shift logic");
  end endgenerate

  // State update policy based on previous window
  genvar k;
  generate
    for (k=0; k<WIDTH; k++) begin : G_STATE
      assert property ((debounce_reg[k] == {N{1'b0}}) |=> state[k] == 1'b0);
      assert property ((debounce_reg[k] == {N{1'b1}}) |=> state[k] == 1'b1);
      assert property ((debounce_reg[k] != {N{1'b0}} && debounce_reg[k] != {N{1'b1}}) |=> $stable(state[k]));
      // Any change in state must be justified by a saturated window in the prior cycle
      assert property (state[k] != $past(state[k]) |-> ($past(debounce_reg[k]) == {N{1'b0}} || $past(debounce_reg[k]) == {N{1'b1}}));
    end
  endgenerate

  // Lightweight coverage
  cover property (@(posedge clk) !rst ##1 (cnt_reg == 24'd0)); // sampling tick seen
  cover property (@(posedge clk) !rst && $past(cnt_reg) != 24'd0 && cnt_reg == 24'd0); // wrap or overflow to 0
  generate
    for (k=0; k<WIDTH; k++) begin : G_COV
      cover property (state[k] == 1'b0 ##[1:$] state[k] == 1'b1);
      cover property (state[k] == 1'b1 ##[1:$] state[k] == 1'b0);
      cover property ((debounce_reg[k] == {N{1'b1}}) ##1 state[k] == 1'b1);
      cover property ((debounce_reg[k] == {N{1'b0}}) ##1 state[k] == 1'b0);
    end
  endgenerate

endmodule