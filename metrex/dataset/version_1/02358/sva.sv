// SVA for shift_register
module shift_register_sva (
    input  logic        clk,
    input  logic        reset,
    input  logic        enable,
    input  logic        shift,
    input  logic [7:0]  parallel_in,
    input  logic [7:0]  parallel_out,
    ref    logic [7:0]  pipeline_reg [0:2]
);
  default clocking cb @ (posedge clk); endclocking

  // Combinational output mirrors reg0
  a_out_mirror: assert property (parallel_out == pipeline_reg[0]);

  // Synchronous reset clears on next cycle
  a_reset_clears: assert property (reset |=> (pipeline_reg[0]==8'h00 &&
                                              pipeline_reg[1]==8'h00 &&
                                              pipeline_reg[2]==8'h00 &&
                                              parallel_out   ==8'h00));

  // When disabled, hold state and output
  a_hold_when_disabled: assert property (disable iff (reset)
    !enable |=> ($stable(pipeline_reg[0]) &&
                 $stable(pipeline_reg[1]) &&
                 $stable(pipeline_reg[2]) &&
                 $stable(parallel_out)));

  // Functional updates when enabled: reg0/reg1 mapping
  a_update_reg01: assert property (disable iff (reset)
    enable |=> (
      pipeline_reg[0][0]   == $past(pipeline_reg[2][7])   &&
      pipeline_reg[0][7:1] == $past(pipeline_reg[1][6:0]) &&
      pipeline_reg[1][0]   == $past(pipeline_reg[0][7])   &&
      pipeline_reg[1][7:1] == $past(pipeline_reg[2][6:0])
    ));

  // Functional updates when enabled: reg2 shift/insert behavior
  a_update_reg2: assert property (disable iff (reset)
    enable |=> (
      pipeline_reg[2][7]   == $past(shift ? parallel_in[0] : pipeline_reg[1][0]) &&
      pipeline_reg[2][6:0] == $past(pipeline_reg[2][7:1])
    ));

  // No X/Z on state after reset deassertion
  a_no_x_on_state: assert property (disable iff (reset)
    !$isunknown({pipeline_reg[0], pipeline_reg[1], pipeline_reg[2], parallel_out}));

  // Coverage
  c_seen_disable:           cover property (!enable);
  c_seen_enable_shift0:     cover property (enable && !shift);
  c_seen_enable_shift1_0:   cover property (enable && shift && (parallel_in[0]==1'b0));
  c_seen_enable_shift1_1:   cover property (enable && shift && (parallel_in[0]==1'b1));
  c_injected_bit_to_reg0:   cover property (enable && shift ##1 enable &&
                                            (pipeline_reg[0][0] == $past(parallel_in[0])));
endmodule

// Bind into DUT
bind shift_register shift_register_sva sva (
  .clk(clk),
  .reset(reset),
  .enable(enable),
  .shift(shift),
  .parallel_in(parallel_in),
  .parallel_out(parallel_out),
  .pipeline_reg(pipeline_reg)
);