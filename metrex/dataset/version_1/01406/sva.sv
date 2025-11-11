// SVA for shift_register
// Binds into the DUT and checks/cover key behaviors concisely.

module shift_register_sva(
    input  logic        clk,
    input  logic        areset,
    input  logic        load,
    input  logic        ena,
    input  logic [3:0]  data,
    input  logic [3:0]  q,
    input  logic [3:0]  q1, q2, q3, q4
);
  default clocking cb @(posedge clk); endclocking

  bit past_valid;
  initial past_valid = 1'b0;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // Reset clears all flops on the next clock
  assert property (areset |=> (q1==4'b0 && q2==4'b0 && q3==4'b0 && q4==4'b0));

  // Idle: hold state
  assert property (disable iff (!past_valid || areset)
                   (!load && !ena) |=> $stable({q1,q2,q3,q4}));

  // Load only: q1 takes data, others hold
  assert property (disable iff (!past_valid || areset)
                   (load && !ena) |=> (q1==$past(data) && $stable({q2,q3,q4})));

  // Load+ena: q1=data, tail cleared
  assert property (disable iff (!past_valid || areset)
                   (load && ena) |=> (q1==$past(data) && q2==4'b0 && q3==4'b0 && q4==4'b0));

  // Shift only: cascade forward, q4 clears
  assert property (disable iff (!past_valid || areset)
                   (!load && ena) |=> (q1==$past(q2) && q2==$past(q3) && q3==$past(q4) && q4==4'b0));

  // Output mapping (detects width/concat mistakes)
  assert property (q === q1);

  // With 4 consecutive shifts (no load), chain drains to zero
  assert property (disable iff (!past_valid || areset)
                   (!load && ena)[*4] |=> (q1==4'b0 && q2==4'b0 && q3==4'b0 && q4==4'b0));

  // Functional coverage of all branches and a typical scenario
  cover property (areset);
  cover property (disable iff (areset) (load && !ena));
  cover property (disable iff (areset) (load && ena));
  cover property (disable iff (areset) (!load && ena));
  cover property (disable iff (areset) (!load && !ena));
  cover property (disable iff (areset) (load && ena) ##1 (!load && ena)[*4]);
endmodule

bind shift_register shift_register_sva u_shift_register_sva(
  .clk(clk), .areset(areset), .load(load), .ena(ena), .data(data),
  .q(q), .q1(q1), .q2(q2), .q3(q3), .q4(q4)
);