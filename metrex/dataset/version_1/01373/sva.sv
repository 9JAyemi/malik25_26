// SVA checker for module counter
module counter_sva (
  input  logic       clk,
  input  logic       reset,
  ref    logic [7:0] counter,
  ref    logic [7:0] waveforms,
  ref    logic       interrupt_event,
  ref    logic [3:0] state
);
  localparam logic [3:0] S0 = 4'b0000;
  localparam logic [3:0] S1 = 4'b0001;
  localparam logic [3:0] S2 = 4'b0010;

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Asynchronous reset clears (sample after NBA)
  assert property (@(posedge reset) ##0 (counter==8'h00 && waveforms==8'h00 && interrupt_event==1'b0 && state==S0));

  // Counter increments and wraps
  assert property (counter == $past(counter) + 8'd1);
  assert property (($past(counter)==8'hFF) |-> (counter==8'h00));

  // State encoding valid
  assert property (state inside {S0,S1,S2});

  // State transitions and holds
  assert property ((state==S0 && counter!=8'd127) |=> state==S0);
  assert property ((state==S0 && counter==8'd127) |=> state==S1);

  assert property ((state==S1 && counter!=8'd191) |=> state==S1);
  assert property ((state==S1 && counter==8'd191) |=> state==S2);

  assert property ((state==S2) |=> state==S2); // stays in S2

  // Waveforms correctness per state
  assert property ((state==S0) |-> (waveforms == {8{counter[6]}}));
  assert property ((state==S1) |-> (waveforms == (counter[2:0] << 5)));
  assert property ((state==S2) |-> (waveforms[7:6]==2'b00 && waveforms[5:0]=={6{counter[6]}}));

  // interrupt_event behavior: only rises at S2 && counter==255, never falls
  assert property ($rose(interrupt_event) |-> $past(state==S2 && counter==8'hFF));
  assert property ($past(state==S2 && counter==8'hFF) |-> interrupt_event);
  assert property (! $fell(interrupt_event));

  // Coverage: full progression to interrupt and S2 wrap
  cover property ((state==S0 && counter==8'd0)
                  ##[1:128] (state==S1 && counter==8'd128)
                  ##[1:64]  (state==S2 && counter==8'd192)
                  ##[1:64]  $rose(interrupt_event));

  cover property (state==S2 ##1 counter==8'hFF ##1 (counter==8'h00 && state==S2));
endmodule

// Bind into DUT (requires tool support for ref port binding to internal 'state')
bind counter counter_sva u_counter_sva (
  .clk(clk),
  .reset(reset),
  .counter(counter),
  .waveforms(waveforms),
  .interrupt_event(interrupt_event),
  .state(state)
);