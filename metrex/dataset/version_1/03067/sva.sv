// SVA for moore_state_machine
module moore_state_machine_sva (
  input logic        clk,
  input logic        reset,      // active-low
  input logic        input_bit,
  input logic [1:0]  state
);

  default clocking cb @(posedge clk); endclocking

  // Asynchronous reset puts state to 00 immediately
  property p_async_reset_immediate;
    @(negedge reset) ##0 (state == 2'b00);
  endproperty
  assert property (p_async_reset_immediate);

  // While in reset, state holds at 00 on every clk
  assert property (@cb !reset |-> state == 2'b00);

  // State encoding must be legal and known
  assert property (@cb !$isunknown(state));
  assert property (@cb state inside {2'b00,2'b01,2'b10});

  // Next-state function (when not in reset, using previous cycle inputs)
  property p_next_from_C;
    @cb disable iff (!reset || !$past(reset))
      ($past(state)==2'b00) |-> state == ($past(input_bit) ? 2'b00 : 2'b01);
  endproperty
  assert property (p_next_from_C);

  property p_next_from_B;
    @cb disable iff (!reset || !$past(reset))
      ($past(state)==2'b01) |-> state == ($past(input_bit) ? 2'b01 : 2'b10);
  endproperty
  assert property (p_next_from_B);

  property p_next_from_A;
    @cb disable iff (!reset || !$past(reset))
      ($past(state)==2'b10) |-> state == ($past(input_bit) ? 2'b10 : 2'b01);
  endproperty
  assert property (p_next_from_A);

  // Coverage: reach all states
  cover property (@cb disable iff (!reset) state==2'b00);
  cover property (@cb disable iff (!reset) state==2'b01);
  cover property (@cb disable iff (!reset) state==2'b10);

  // Coverage: all transitions under both input values
  cover property (@cb disable iff (!reset || !$past(reset))
                  $past(state)==2'b00 && !$past(input_bit) && state==2'b01);
  cover property (@cb disable iff (!reset || !$past(reset))
                  $past(state)==2'b00 &&  $past(input_bit) && state==2'b00);

  cover property (@cb disable iff (!reset || !$past(reset))
                  $past(state)==2'b01 && !$past(input_bit) && state==2'b10);
  cover property (@cb disable iff (!reset || !$past(reset))
                  $past(state)==2'b01 &&  $past(input_bit) && state==2'b01);

  cover property (@cb disable iff (!reset || !$past(reset))
                  $past(state)==2'b10 && !$past(input_bit) && state==2'b01);
  cover property (@cb disable iff (!reset || !$past(reset))
                  $past(state)==2'b10 &&  $past(input_bit) && state==2'b10);

endmodule

bind moore_state_machine moore_state_machine_sva sva_i (
  .clk(clk),
  .reset(reset),
  .input_bit(input_bit),
  .state(state)
);