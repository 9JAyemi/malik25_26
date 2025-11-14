// Bind these assertions to the DUT
bind delay_inv delay_inv_sva #(.D(5)) u_delay_inv_sva (
  .clk     (clk),
  .A       (A),
  .Y       (Y),
  .VPWR    (VPWR),
  .VGND    (VGND),
  .delay_reg(delay_reg),
  .out_reg (out_reg)
);

// SVA checker
module delay_inv_sva #(int unsigned D=5) (
  input logic clk,
  input logic A,
  input logic Y,
  input logic VPWR,
  input logic VGND,
  input logic [D-1:0] delay_reg,
  input logic out_reg
);
  default clocking cb @(posedge clk); endclocking

  // Warm-up counter to safely use $past
  logic [$clog2(D+1):0] cyc = '0;
  always_ff @(posedge clk) cyc <= cyc + 1'b1;

  wire power_good = (VPWR === 1'b1) && (VGND === 1'b0);

  // Power rails must be valid
  a_power_good: assert property (power_good);

  // Output wire must mirror the output register
  a_y_tie: assert property (Y === out_reg);

  // No mid-cycle updates (all state should only change on posedge clk)
  a_no_midcycle: assert property (@(negedge clk) $stable({Y, out_reg, delay_reg}));

  // out_reg captures prior delay_reg[MSB]
  a_out_seq: assert property (disable iff (!power_good || cyc < 1)
                              out_reg == $past(delay_reg[D-1]));

  // Shift chain correctness
  genvar i;
  generate
    for (i = 1; i < D; i++) begin : g_shift
      a_shift: assert property (disable iff (!power_good || cyc < 1)
                                delay_reg[i] == $past(delay_reg[i-1]));
    end
  endgenerate

  // Input bit enters stage 0
  a_shift_in: assert property (disable iff (!power_good || cyc < 1)
                               delay_reg[0] == $past(A));

  // End-to-end latency: Y equals A delayed by D cycles
  a_latency: assert property (disable iff (!power_good || cyc < D)
                              Y == $past(A, D));

  // Functional coverage
  c_rise: cover property (disable iff (!power_good) (cyc >= D) && $rose(A) ##D $rose(Y));
  c_fall: cover property (disable iff (!power_good) (cyc >= D) && $fell(A) ##D $fell(Y));
  c_hold: cover property (disable iff (!power_good) (cyc >= D) && $stable(A)[*D] ##1 $stable(Y));
endmodule