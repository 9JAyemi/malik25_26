// SVA for clock_reset_gen
// Bind this module to the DUT: bind clock_reset_gen clock_reset_gen_sva sv();

module clock_reset_gen_sva;

  // Access DUT scope (clk_in, rst_in, clk_out, rst_out, counter)
  bit past_valid_ci;
  initial past_valid_ci = 0;
  always @(posedge clk_in) past_valid_ci <= 1;

  // 1) Counter stays in {0,1,2} and follows 0->1->2->0
  assert property (@(posedge clk_in)
    past_valid_ci |-> counter inside {32'd0,32'd1,32'd2});

  assert property (@(posedge clk_in)
    past_valid_ci |-> (
      ($past(counter)==32'd0 && counter==32'd1) ||
      ($past(counter)==32'd1 && counter==32'd2) ||
      ($past(counter)==32'd2 && counter==32'd0)
    )
  );

  // 2) clk_out update is a function of previous counter value
  assert property (@(posedge clk_in)
    past_valid_ci && $past(counter)==32'd1 |-> clk_out==1'b1);

  assert property (@(posedge clk_in)
    past_valid_ci && $past(counter)==32'd2 |-> clk_out==1'b0);

  assert property (@(posedge clk_in)
    past_valid_ci && $past(counter)==32'd0 |-> clk_out==$past(clk_out));

  // 3) Edge correlation for clk_out
  assert property (@(posedge clk_in)
    past_valid_ci && $rose(clk_out) |-> $past(counter)==32'd1);

  assert property (@(posedge clk_in)
    past_valid_ci && $fell(clk_out) |-> $past(counter)==32'd2);

  // 4) clk_out pulse is exactly 1 clk_in cycle high and repeats every 3 clk_in cycles
  assert property (@(posedge clk_in)
    past_valid_ci && $rose(clk_out) |-> ##1 !clk_out);

  assert property (@(posedge clk_in)
    past_valid_ci && $rose(clk_out) |-> ! $rose(clk_out) ##1 ! $rose(clk_out) ##1 $rose(clk_out));

  // 5) rst_out synchronous to clk_out and changes only on clk_out posedges
  assert property (@(posedge clk_out) rst_out == rst_in);

  assert property (@(posedge clk_in)
    past_valid_ci && !$rose(clk_out) |-> rst_out == $past(rst_out));

  assert property (@(posedge clk_in)
    past_valid_ci && $changed(rst_out) |-> $rose(clk_out));

  // 6) No X on critical controls once sequence starts
  assert property (@(posedge clk_in)
    past_valid_ci |-> !$isunknown(counter[2:0]) && !$isunknown(clk_out));

  // Coverage
  cover property (@(posedge clk_in)
    past_valid_ci && $past(counter)==32'd0 ##1 counter==32'd1 ##1 counter==32'd2 ##1 counter==32'd0);

  cover property (@(posedge clk_in)
    past_valid_ci && $rose(clk_out) ##3 $rose(clk_out));

  cover property (@(posedge clk_out) rst_out==1);
  cover property (@(posedge clk_out) rst_out==0);

endmodule

bind clock_reset_gen clock_reset_gen_sva sv();