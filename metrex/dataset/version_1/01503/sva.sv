// SVA for digital_clock
// Bind this checker to the DUT:
// bind digital_clock digital_clock_sva #(.SEC_CNT(SEC_CNT), .MIN_CNT(MIN_CNT), .HOUR_CNT(HOUR_CNT)) u_digital_clock_sva (.*);

module digital_clock_sva #(
  parameter int SEC_CNT  = 60,
  parameter int MIN_CNT  = 60,
  parameter int HOUR_CNT = 24
)(
  input logic        CLK,
  input logic        RST,
  input logic [5:0]  SEC,
  input logic [5:0]  MIN,
  input logic [4:0]  HOUR
);

  default clocking cb @(posedge CLK); endclocking

  // X-free and range safety
  assert property (disable iff (RST) !$isunknown({SEC,MIN,HOUR}));
  assert property (SEC < SEC_CNT && MIN < MIN_CNT && HOUR < HOUR_CNT);

  // Synchronous reset forces zeros
  assert property (RST |-> (SEC==0 && MIN==0 && HOUR==0));

  // Second tick increments and holds MIN/HOUR
  assert property (disable iff (RST)
                   (SEC != SEC_CNT-1) |=> (SEC == $past(SEC)+1 && $stable(MIN) && $stable(HOUR)));

  // Second rollover -> minute increments (hour holds)
  assert property (disable iff (RST)
                   (SEC == SEC_CNT-1 && MIN != MIN_CNT-1)
                   |=> (SEC==0 && MIN==$past(MIN)+1 && $stable(HOUR)));

  // Minute rollover -> hour increments
  assert property (disable iff (RST)
                   (SEC == SEC_CNT-1 && MIN == MIN_CNT-1 && HOUR != HOUR_CNT-1)
                   |=> (SEC==0 && MIN==0 && HOUR==$past(HOUR)+1));

  // Hour rollover -> all zero
  assert property (disable iff (RST)
                   (SEC == SEC_CNT-1 && MIN == MIN_CNT-1 && HOUR == HOUR_CNT-1)
                   |=> (SEC==0 && MIN==0 && HOUR==0));

  // SEC reaches 0 only due to rollover (outside reset)
  assert property (disable iff (RST) (SEC==0) |-> ($past(SEC)==SEC_CNT-1));

  // MIN changes only on SEC rollover; single-step semantics
  assert property (disable iff (RST) $changed(MIN) |-> ($past(SEC)==SEC_CNT-1));
  assert property (disable iff (RST) ($changed(MIN) && MIN!=0) |-> (MIN==$past(MIN)+1));
  assert property (disable iff (RST) ($changed(MIN) && MIN==0)  |-> ($past(MIN)==MIN_CNT-1));

  // HOUR changes only on SEC+MIN rollover; single-step semantics
  assert property (disable iff (RST) $changed(HOUR) |-> ($past(SEC)==SEC_CNT-1 && $past(MIN)==MIN_CNT-1));
  assert property (disable iff (RST) ($changed(HOUR) && HOUR!=0) |-> (HOUR==$past(HOUR)+1));
  assert property (disable iff (RST) ($changed(HOUR) && HOUR==0)  |-> ($past(HOUR)==HOUR_CNT-1));

  // Coverage
  cover property (RST ##1 !RST);
  cover property (disable iff (RST) (SEC < SEC_CNT-1) ##1 (SEC == $past(SEC)+1));
  cover property (disable iff (RST) (SEC==SEC_CNT-1 && MIN!=MIN_CNT-1) ##1 (SEC==0 && MIN==$past(MIN)+1));
  cover property (disable iff (RST) (SEC==SEC_CNT-1 && MIN==MIN_CNT-1 && HOUR!=HOUR_CNT-1)
                                 ##1 (SEC==0 && MIN==0 && HOUR==$past(HOUR)+1));
  cover property (disable iff (RST) (SEC==SEC_CNT-1 && MIN==MIN_CNT-1 && HOUR==HOUR_CNT-1)
                                 ##1 (SEC==0 && MIN==0 && HOUR==0));

endmodule