// SVA for scp_sender
module scp_sender_sva(
  input logic USER_CLK,
  input logic CHANNEL_UP,
  input logic rst_r,
  input logic start_r,
  input logic run_r
);
  default clocking cb @(posedge USER_CLK); endclocking

  // Combinational equivalences under CHANNEL_UP
  assert property (rst_r == !CHANNEL_UP);
  assert property (CHANNEL_UP |-> (start_r == $past(rst_r)));
  assert property (CHANNEL_UP |-> (run_r   == ($past(start_r) || $past(run_r))));

  // Behavior when CHANNEL_UP is low
  assert property (!CHANNEL_UP |-> (rst_r && !start_r && !run_r));

  // Start pulse and run sequencing around CHANNEL_UP rising edge
  assert property ($rose(CHANNEL_UP) |-> (!rst_r && start_r && !run_r));
  assert property ($rose(CHANNEL_UP) |=> (!start_r && run_r));

  // start_r is a single-cycle pulse; only occurs on CHANNEL_UP rise
  assert property (start_r |-> $rose(CHANNEL_UP));
  assert property (start_r |=> !start_r);

  // run_r stickiness and cause
  assert property (CHANNEL_UP && $past(CHANNEL_UP) && $past(run_r) |-> run_r);
  assert property ($rose(run_r) |-> CHANNEL_UP && $past(start_r));

  // Coverage
  sequence start_then_run;
    $rose(CHANNEL_UP)
    ##0 (start_r && !run_r && !rst_r)
    ##1 (!start_r && run_r && !rst_r);
  endsequence
  cover property (start_then_run);

  sequence run_then_down;
    (CHANNEL_UP && run_r)
    ##1 $fell(CHANNEL_UP)
    ##0 (!CHANNEL_UP && rst_r && !start_r && !run_r);
  endsequence
  cover property (run_then_down);

  cover property ($rose(run_r) ##1 (CHANNEL_UP && run_r)[*3]);
endmodule

bind scp_sender scp_sender_sva sva_i(.*);