// SVA for rotator: bind these assertions to the DUT

module rotator_sva #(parameter int N = 100) (
  input  logic              clk,
  input  logic              load,
  input  logic [1:0]        ena,
  input  logic [N-1:0]      data,
  input  logic [N-1:0]      q,
  input  logic [N-1:0]      shift_reg
);

  default clocking cb @(posedge clk); endclocking

  // past-valid tracking (and depth for 100-cycle periodicity checks)
  logic past_valid;
  int unsigned cyc;
  initial begin past_valid = 1'b0; cyc = 0; end
  always_ff @(posedge clk) begin
    past_valid <= 1'b1;
    if (cyc < N) cyc <= cyc + 1;
  end
  wire past_100_valid = (cyc >= N);

  default disable iff (!past_valid);

  // X/Z checks (at clock edges)
  ASSERT_NO_X_INPUTS: assert property (!$isunknown({load, ena, data})));
  ASSERT_NO_X_Q:      assert property (!$isunknown(q));

  // q must mirror shift_reg (combinational assignment)
  ASSERT_Q_EQ_SHIFTREG: assert property (q == shift_reg);

  // Load dominates enables
  ASSERT_LOAD_NEXT_Q: assert property (load |=> q == $past(data));

  // Idle: no change
  ASSERT_IDLE_HOLDS: assert property (!load && ena == 2'b00 |=> q == $past(q));

  // Rotate right by 1 when ena[0] is asserted (regardless of ena[1])
  ASSERT_ROTR1: assert property (!load && ena[0]
                                 |=> q == { $past(q[0]), $past(q[N-1:1]) });

  // Rotate left by 1 when only ena[1] is asserted
  ASSERT_ROTL1: assert property (!load && !ena[0] && ena[1]
                                 |=> q == { $past(q[N-2:0]), $past(q[N-1]) });

  // Rotation preserves bit count
  ASSERT_COUNTONES_PRESERVED: assert property (!load && ena != 2'b00
                                              |=> $countones(q) == $countones($past(q)));

  // Periodicity: 100 single-bit rotations restore original
  ASSERT_ROTR1_PERIODIC: assert property ( disable iff (!past_100_valid)
                                          ((!load && ena == 2'b01) [*N]) |=> q == $past(q, N) );
  ASSERT_ROTL1_PERIODIC: assert property ( disable iff (!past_100_valid)
                                          ((!load && ena == 2'b10) [*N]) |=> q == $past(q, N) );

  // Coverage: hit each operation and both-bits-high case (documents priority)
  COVER_LOAD:  cover property (load);
  COVER_ROTR1: cover property (!load && ena == 2'b01 ##1
                               q == { $past(q[0]), $past(q[N-1:1]) });
  COVER_ROTL1: cover property (!load && ena == 2'b10 ##1
                               q == { $past(q[N-2:0]), $past(q[N-1]) });
  COVER_BOTHBITS_PRIORITY: cover property (!load && ena == 2'b11 ##1
                               q == { $past(q[0]), $past(q[N-1:1]) });

endmodule

// Bind to DUT (access internal shift_reg for a strong mirror check)
bind rotator rotator_sva #(.N(100)) rotator_sva_i (
  .clk(clk),
  .load(load),
  .ena(ena),
  .data(data),
  .q(q),
  .shift_reg(shift_reg)
);