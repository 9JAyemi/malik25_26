// SVA for multiplier/barrel_shifter
// Bind-in, concise, focused on correctness, latency, stability, and coverage.

bind multiplier multiplier_sva();

module multiplier_sva;
  // Access DUT signals directly via bind scope
  // clk, rst, in1, in2, select, out
  // product, temp_in2, shifted_in2, in1_prev, in2_prev

  // track when $past is valid
  logic past_valid;
  always @(posedge clk) begin
    if (rst) past_valid <= 1'b0;
    else     past_valid <= 1'b1;
  end

  // Sanity: no X on primary inputs; reset drives out to 0
  a_no_x_inputs: assert property (@(posedge clk) !$isunknown({rst,in1,in2,select}));
  a_rst_out0   : assert property (@(posedge clk) rst |-> out == 16'h0);

  // Prev-registers must reflect one-cycle-old inputs
  a_prev_regs_update: assert property (@(posedge clk) disable iff (rst)
                                       (in1_prev == $past(in1) && in2_prev == $past(in2)));

  // Barrel shifter correctness at the multiplier boundary
  a_barrel_eq: assert property (@(posedge clk) disable iff (rst)
                                temp_in2 == (in2 << select));

  // Wire connectivity (as coded) for the second shift stage
  a_shifted_in2_conn: assert property (@(posedge clk)
                                       shifted_in2 == (temp_in2 << select));

  // Micro-arch schedule: when DUT decides to update (in1/in2 changed),
  // product must take the proper operands on the next cycle
  a_product_uses_shifted: assert property (@(posedge clk) disable iff (rst)
                                           ((in1 != in1_prev) || (in2 != in2_prev))
                                           |=> product == $past(in1 * shifted_in2));

  // Functional spec (single-shift): out must reflect in1*(in2<<select) one cycle after ANY operand change
  // (catches double-shift bug, missing select gating, and wrong latency)
  a_out_updates_on_change: assert property (@(posedge clk) disable iff (rst)
                                           ( ((in1 != in1_prev) || (in2 != in2_prev)) ||
                                             (past_valid && (select != $past(select))) )
                                           |=> out == $past(in1 * (in2 << select)));

  // Stability when nothing changed
  a_out_holds_when_no_change: assert property (@(posedge clk) disable iff (rst)
                                              ((in1 == in1_prev) && (in2 == in2_prev) &&
                                               past_valid && (select == $past(select)))
                                              |=> $stable(out));

  // Output should not be X/Z after reset is released
  a_no_x_out: assert property (@(posedge clk) disable iff (rst) !$isunknown(out));

  // Coverage: observe correct update after change
  c_change_then_correct: cover property (@(posedge clk) disable iff (rst)
                                        ( ((in1 != in1_prev) || (in2 != in2_prev)) ||
                                          (past_valid && (select != $past(select))) )
                                        ##1 (out == $past(in1 * (in2 << select))));

  // Coverage: hit all shift amounts
  genvar gi;
  generate
    for (gi = 0; gi < 8; gi++) begin : C_SEL
      c_sel_val: cover property (@(posedge clk) disable iff (rst) select == gi[2:0]);
    end
  endgenerate
endmodule