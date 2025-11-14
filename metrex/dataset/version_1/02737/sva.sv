// SVA for deserializer
module deserializer_sva #(parameter int BITS=32, BITS_COUNTER=8) (
  input  logic                      clk,
  input  logic                      reset,
  input  logic                      enable,
  input  logic                      in,
  input  logic [BITS_COUNTER-1:0]   framesize,
  input  logic                      complete,
  input  logic [BITS-1:0]           out,
  input  logic [BITS_COUNTER-1:0]   counter
);

default clocking cb @(posedge clk); endclocking
`define DISABLE disable iff (reset)

// Static/param checks
initial begin
  assert (BITS <= (1<<BITS_COUNTER)) else $error("BITS must be <= 2**BITS_COUNTER");
end

// Reset drives known state next cycle (sync reset)
assert property (@(posedge clk) reset |=> (out=='0 && counter=='0 && complete==1'b0));

// While active and not complete, the written index is in-range (use $past(counter))
assert property (@(posedge clk) `DISABLE (enable && !complete) |-> ($past(counter) < BITS));

// Counter increments by exactly 1 when capturing
assert property (@(posedge clk) `DISABLE (enable && !complete) |=> counter == $past(counter)+1);

// Only the targeted bit may change, and it reflects 'in'
assert property (@(posedge clk) `DISABLE
  (enable && !complete) |=> (
    (out == $past(out)) ||
    ($onehot(out ^ $past(out)) && out[$past(counter)] == $past(in))
  )
);

// No updates when stalled (complete==1) or disabled (enable==0)
assert property (@(posedge clk) `DISABLE ((!enable) || complete) |=> ($stable(counter) && $stable(out)));

// Complete rises only because counter matched framesize (prior cycle)
assert property (@(posedge clk) `DISABLE $rose(complete) |-> $past(enable && (counter==framesize)));

// Complete is sticky while enable stays high
assert property (@(posedge clk) `DISABLE (enable && complete) |=> complete);

// Complete clears when enable deasserts
assert property (@(posedge clk) `DISABLE (!enable) |=> (complete==1'b0));

// Framesize must fit within BITS
assert property (@(posedge clk) `DISABLE framesize < BITS);

// Coverage: normal frame completes within BITS cycles
cover property (@(posedge clk) `DISABLE (enable && (framesize>0) && !complete) ##[1:BITS] $rose(complete));
// Coverage: clear after disable
cover property (@(posedge clk) `DISABLE $rose(complete) ##1 !enable ##1 (complete==0));
// Coverage: zero-length frame
cover property (@(posedge clk) `DISABLE (enable && framesize==0) ##1 $rose(complete));

endmodule

bind deserializer deserializer_sva #(.BITS(BITS), .BITS_COUNTER(BITS_COUNTER)) deserializer_sva_i (
  .clk(clk), .reset(reset), .enable(enable), .in(in),
  .framesize(framesize), .complete(complete), .out(out), .counter(counter)
);