module Mealy_sva #(
  parameter int n = 4,
  parameter int m = 2,
  parameter int s = 4
)(
  input logic [n-1:0] in,
  input logic clk,
  input logic [m-1:0] out,
  input logic [s-1:0] state
);

  // From state 0 with in[0]&in[1], next state is 1 and out=2'b11.
  check_s0_take_when_both: assert property (
    @(posedge clk) (state == 0 && in[0] && in[1]) |=> (state == 1 && out[1:0] == 2'b11)
  );

  // From state 0 with !(in[0]&in[1]), stay in 0 and out=2'b00.
  check_s0_stay_when_not_both: assert property (
    @(posedge clk) (state == 0 && !(in[0] && in[1])) |=> (state == 0 && out[1:0] == 2'b00)
  );

  // From state 1 with in[0]||in[1], next state is 2 and out=2'b10.
  check_s1_take_when_any: assert property (
    @(posedge clk) (state == 1 && (in[0] || in[1])) |=> (state == 2 && out[1:0] == 2'b10)
  );

  // From state 1 with !(in[0]||in[1]), stay in 1 and out=2'b01.
  check_s1_stay_when_none: assert property (
    @(posedge clk) (state == 1 && !(in[0] || in[1])) |=> (state == 1 && out[1:0] == 2'b01)
  );

  // From state 2 with in[2], next state is 3 and out=2'b01.
  check_s2_take_when_in2: assert property (
    @(posedge clk) (state == 2 && in[2]) |=> (state == 3 && out[1:0] == 2'b01)
  );

  // From state 2 with !in[2], stay in 2 and out=2'b10.
  check_s2_stay_when_not_in2: assert property (
    @(posedge clk) (state == 2 && !in[2]) |=> (state == 2 && out[1:0] == 2'b10)
  );

  // From state 3 with in[3], next state is 0 and out=2'b10.
  check_s3_take_when_in3: assert property (
    @(posedge clk) (state == 3 && in[3]) |=> (state == 0 && out[1:0] == 2'b10)
  );

  // From state 3 with !in[3], stay in 3 and out=2'b01.
  check_s3_stay_when_not_in3: assert property (
    @(posedge clk) (state == 3 && !in[3]) |=> (state == 3 && out[1:0] == 2'b01)
  );

  // If previous state not in {0,1,2,3}, then state and out hold.
  check_unhandled_state_holds: assert property (
    @(posedge clk) !($past(state) inside {0,1,2,3}) |-> (state == $past(state) && out == $past(out))
  );

  // If previous state was 1/2/3, out is never 2'b11.
  check_prev_not_s0_never_out11: assert property (
    @(posedge clk) ($past(state) inside {1,2,3}) |-> (out[1:0] != 2'b11)
  );

  // If previous state was 1/2/3, out is never 2'b00.
  check_prev_not_s0_never_out00: assert property (
    @(posedge clk) ($past(state) inside {1,2,3}) |-> (out[1:0] != 2'b00)
  );

endmodule