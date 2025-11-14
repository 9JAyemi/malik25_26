// SVA for the provided design. Bind to top_module to check all key behaviors.

module top_module_sva (
  input  logic        clk,
  input  logic        reset,
  input  logic        up_down,
  input  logic [3:0]  D,
  input  logic        select,
  input  logic [7:0]  q,
  input  logic [7:0]  up_down_out,
  input  logic [3:0]  left_rotator_out
);
  default clocking cb @(posedge clk); endclocking

  logic past_valid;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // Sanity: no X/Z on key signals after first cycle
  ap_known: assert property (past_valid |-> !$isunknown({reset,up_down,select,D,up_down_out,left_rotator_out,q}));

  // up_down_counter: synchronous reset and +/-1 step
  ap_udc_reset: assert property (reset |-> up_down_out == 8'h00);
  ap_udc_up:    assert property (past_valid && !reset &&  up_down |-> up_down_out == $past(up_down_out) + 8'd1);
  ap_udc_down:  assert property (past_valid && !reset && !up_down |-> up_down_out == $past(up_down_out) - 8'd1);

  // Wrap-around coverage
  cp_wrap_up:   cover  property (past_valid && !reset && (up_down_out==8'hFF) && up_down ##1 !reset && (up_down_out==8'h00));
  cp_wrap_down: cover  property (past_valid && !reset && (up_down_out==8'h00) && !up_down ##1 !reset && (up_down_out==8'hFF));

  // left_rotator: enforce true left-rotate by 1 (q = {D[2:0], D[3]})
  ap_lrot: assert property (left_rotator_out == {D[2:0], D[3]});

  // functional_module: muxing behavior and zeroed low nibble when select==0
  ap_mux:  assert property (q == (select ? up_down_out : {left_rotator_out, 4'b0000}));
  ap_zero_low_when_sel0: assert property (!select |-> q[3:0] == 4'h0);

  // Mux path coverage
  cp_sel1: cover property (select && (q == up_down_out));
  cp_sel0: cover property (!select && (q == {left_rotator_out, 4'h0}));
endmodule

bind top_module top_module_sva tmsva (
  .clk             (clk),
  .reset           (reset),
  .up_down         (up_down),
  .D               (D),
  .select          (select),
  .q               (q),
  .up_down_out     (up_down_out),
  .left_rotator_out(left_rotator_out)
);