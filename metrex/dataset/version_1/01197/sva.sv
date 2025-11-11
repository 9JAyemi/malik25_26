// SVA for input_output_module
// Bind this file to the DUT. Focused, high-signal-quality checks with essential coverage.

module input_output_module_sva (
  input  logic        CLK,
  input  logic [6:0]  Q,
  input  logic [6:0]  inputs_reg,
  input  logic [6:0]  inputs_delayed,
  input  logic [6:0]  delay_counter,
  input  logic [2:0]  input_counter,
  input  logic [1:0]  state_counter,
  input  logic        Q_delayed,
  input  logic        Q_delayed_reg
);

  default clocking cb @(posedge CLK); endclocking

  bit started;
  initial started = 0;
  always @cb started <= 1;

  // Counter next-state functions
  assert property (@cb disable iff (!started)
    !$isunknown($past(delay_counter)) |->
      delay_counter === (($past(delay_counter)==7'd20) ? 7'd0 : $past(delay_counter)+7'd1)
  );

  assert property (@cb disable iff (!started)
    !$isunknown({$past(delay_counter),$past(input_counter)}) |->
      input_counter === (
        ($past(delay_counter)==7'd20) ?
          ( ($past(input_counter)==3'd7) ? 3'd0 : $past(input_counter)+3'd1 )
        : $past(input_counter)
      )
  );

  assert property (@cb disable iff (!started)
    !$isunknown({$past(delay_counter),$past(input_counter),$past(state_counter)}) |->
      state_counter === (
        ($past(delay_counter)==7'd20 && $past(input_counter)==3'd7) ?
          ( ($past(state_counter)==2'd3) ? 2'd0 : $past(state_counter)+2'd1 )
        : $past(state_counter)
      )
  );

  // Range constraints
  assert property (@cb !$isunknown(delay_counter) |-> delay_counter inside {[7'd0:7'd20]});
  assert property (@cb !$isunknown(input_counter) |-> input_counter inside {[3'd0:3'd7]});
  assert property (@cb !$isunknown(state_counter) |-> state_counter inside {[2'd0:2'd3]});

  // Pipeline/registering checks
  assert property (@cb disable iff (!started) inputs_reg      === $past(Q));
  assert property (@cb                      ) inputs_delayed  === {inputs_reg[0],inputs_reg[1],inputs_reg[2],inputs_reg[3],inputs_reg[4],inputs_reg[5],inputs_reg[6]};
  assert property (@cb                      ) Q_delayed       ==  Q;
  assert property (@cb disable iff (!started) Q_delayed_reg   === $past(Q));

  // Q behavior per state (uses non-overlapped implication due to NBA update)
  assert property (@cb disable iff (!started)
    (state_counter==2'd0) |=> (Q === 7'b1000000)
  );
  assert property (@cb disable iff (!started)
    (state_counter==2'd1) |=> (Q === 7'b0111111)
  );
  assert property (@cb disable iff (!started)
    (state_counter==2'd2) |=> $isunknown(Q)
  );
  assert property (@cb disable iff (!started)
    (state_counter==2'd3) |=> (Q === $past(Q))
  );

  // Essential coverage
  cover property (@cb disable iff (!started) delay_counter == 7'd20);
  cover property (@cb disable iff (!started) input_counter == 3'd7);
  cover property (@cb disable iff (!started) state_counter == 2'd3);
  cover property (@cb disable iff (!started) Q == 7'b1000000);
  cover property (@cb disable iff (!started) Q == 7'b0111111);
  cover property (@cb disable iff (!started) $isunknown(Q));

endmodule

// Bind to DUT type
bind input_output_module input_output_module_sva
(
  .CLK(CLK),
  .Q(Q),
  .inputs_reg(inputs_reg),
  .inputs_delayed(inputs_delayed),
  .delay_counter(delay_counter),
  .input_counter(input_counter),
  .state_counter(state_counter),
  .Q_delayed(Q_delayed),
  .Q_delayed_reg(Q_delayed_reg)
);