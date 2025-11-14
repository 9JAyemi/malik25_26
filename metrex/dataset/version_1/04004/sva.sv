// SVA for SmallBpf
module SmallBpf_sva #(parameter int WIDTH=16, K0_SHIFT=5, K1_SHIFT=5, CLAMP=1)
(
  input  logic                          clk,
  input  logic                          rst,
  input  logic                          en,
  input  logic signed   [WIDTH-1:0]     dataIn,
  input  logic signed   [WIDTH-1:0]     dataOut,
  input  logic signed   [WIDTH-1:0]     acc0, acc1, acc2, acc3,
  input  logic signed   [WIDTH-1:0]     dataInK0, dataInK1,
  input  logic signed   [WIDTH-1:0]     acc0K0, acc1K1, acc2K0, acc3K1
);

  // Signed limits for WIDTH
  localparam signed [WIDTH-1:0] MAX_S = {1'b0,{(WIDTH-1){1'b1}}}; //  0 111..1
  localparam signed [WIDTH-1:0] MIN_S = {1'b1,{(WIDTH-1){1'b0}}}; //  1 000..0

  // Helpers
  let acc0_next(a0,a1,di) = (di <<< K0_SHIFT) - (a0 <<< K0_SHIFT) + (a1 <<< K1_SHIFT);
  let acc1_next(a0,a1)    = (a0 <<< K0_SHIFT) + (a1 <<< K1_SHIFT);
  let acc2_next(a2,a3,a1) = (a2 <<< K0_SHIFT) - (a3 <<< K1_SHIFT) + a1;
  let acc3_next(a3,a1)    = (a3 <<< K1_SHIFT) + a1;
  let saturate(prev,cand) = (CLAMP ? ((prev > MAX_S) ? MAX_S
                                      : ((prev < MIN_S) ? MIN_S : cand))
                                  : cand);

  // Basic hygiene
  a_no_x:        assert property (@(posedge clk) disable iff (rst)
                    !$isunknown({en,dataIn,dataOut,acc0,acc1,acc2,acc3}))
                  else $error("X/Z detected on interface/state");

  // Synchronous reset behavior
  a_reset_clear: assert property (@(posedge clk)
                    rst |=> (acc0==0 && acc1==0 && acc2==0 && acc3==0 && dataOut==0))
                  else $error("Reset did not clear state/outputs");

  // Combinational multipliers (as coded)
  a_mul_wires:   assert property (@(posedge clk)
                    (dataInK0==(dataIn <<< K0_SHIFT)) &&
                    (dataInK1==(dataIn <<< K1_SHIFT)) &&
                    (acc0K0==(acc0 <<< K0_SHIFT))   &&
                    (acc1K1==(acc1 <<< K1_SHIFT))   &&
                    (acc2K0==(acc2 <<< K0_SHIFT))   &&
                    (acc3K1==(acc3 <<< K1_SHIFT)))
                  else $error("Shifted multiply wires mismatch");

  // Hold when disabled
  a_hold_when_dis: assert property (@(posedge clk) disable iff (rst)
                        !en |=> $stable({acc0,acc1,acc2,acc3,dataOut}))
                    else $error("State/output changed while en=0");

  // DataOut pipeline relation (1-cycle from acc2, as coded)
  a_dout_pipe:     assert property (@(posedge clk)
                        $past(en) && !$past(rst) |-> dataOut == $past(acc2))
                    else $error("dataOut not equal to prior acc2 on enabled update");

  // State update equations (including coded clamp behavior)
  a_acc0_next:   assert property (@(posedge clk)
                      $past(en) && !$past(rst) |->
                        acc0 == saturate($past(acc0), acc0_next($past(acc0),$past(acc1),$past(dataIn))))
                  else $error("acc0 update mismatch");

  a_acc1_next:   assert property (@(posedge clk)
                      $past(en) && !$past(rst) |->
                        acc1 == saturate($past(acc1), acc1_next($past(acc0),$past(acc1))))
                  else $error("acc1 update mismatch");

  a_acc2_next:   assert property (@(posedge clk)
                      $past(en) && !$past(rst) |->
                        acc2 == saturate($past(acc2), acc2_next($past(acc2),$past(acc3),$past(acc1))))
                  else $error("acc2 update mismatch");

  a_acc3_next:   assert property (@(posedge clk)
                      $past(en) && !$past(rst) |->
                        acc3 == saturate($past(acc3), acc3_next($past(acc3),$past(acc1))))
                  else $error("acc3 update mismatch");

  // Coverage
  c_reset_seq:     cover property (@(posedge clk) rst ##1 !rst);
  c_enable_pulse:  cover property (@(posedge clk) !rst && !en ##1 en ##1 !en);
  c_dout_changes:  cover property (@(posedge clk) $past(en) && !$past(rst) && $changed(dataOut));
  c_extremes:      cover property (@(posedge clk)
                        (acc0==MAX_S || acc1==MAX_S || acc2==MAX_S || acc3==MAX_S ||
                         acc0==MIN_S || acc1==MIN_S || acc2==MIN_S || acc3==MIN_S));
  c_sign_inputs:   cover property (@(posedge clk) en && dataIn!=0 && dataIn[WIDTH-1]);
  c_sign_inputs2:  cover property (@(posedge clk) en && dataIn!=0 && !dataIn[WIDTH-1]);

endmodule

// Bind to DUT (connect internal signals)
bind SmallBpf SmallBpf_sva #(.WIDTH(WIDTH), .K0_SHIFT(K0_SHIFT), .K1_SHIFT(K1_SHIFT), .CLAMP(CLAMP))
  SmallBpf_sva_i (
    .clk     (clk),
    .rst     (rst),
    .en      (en),
    .dataIn  (dataIn),
    .dataOut (dataOut),
    .acc0    (acc0),
    .acc1    (acc1),
    .acc2    (acc2),
    .acc3    (acc3),
    .dataInK0(dataInK0),
    .dataInK1(dataInK1),
    .acc0K0  (acc0K0),
    .acc1K1  (acc1K1),
    .acc2K0  (acc2K0),
    .acc3K1  (acc3K1)
  );