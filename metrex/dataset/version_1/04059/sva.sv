// SVA for pio_latency
// Bind this checker to the DUT to verify latency, reset, and mux behavior.

module pio_latency_sva
(
  input logic        clk,
  input logic        reset_n,
  input logic [1:0]  address,
  input logic [15:0] in_port,
  input logic [15:0] readdata
);

  // Helper: expected combinational mux output
  function automatic logic [15:0] exp_mux(input logic [1:0] a, input logic [15:0] din);
    return (a == 2'b00) ? din : 16'h0;
  endfunction

  // 1) Asynchronous reset holds readdata at 0 (checked each clk edge while low)
  assert property (@(posedge clk) !reset_n |-> readdata == 16'h0)
    else $error("readdata not 0 during reset");

  // 2) One-cycle latency in steady operation (not the first cycle after reset)
  //    readdata equals previous cycle's mux result
  assert property (@(posedge clk) disable iff (!reset_n)
                   $past(reset_n) |-> readdata == $past(exp_mux(address, in_port)))
    else $error("Latency mismatch: readdata != $past(exp_mux)");

  // 3) First cycle after reset deassert: readdata captures current mux output
  assert property (@(posedge clk) $rose(reset_n) |-> readdata == exp_mux(address, in_port))
    else $error("First-cycle-after-reset capture mismatch");

  // 4) Basic X/Z hygiene on key inputs when not in reset
  assert property (@(posedge clk) disable iff (!reset_n)
                   !$isunknown({address, in_port}))
    else $error("X/Z detected on address or in_port");

  // 5) If previous address != 0, next readdata must be 0
  assert property (@(posedge clk) disable iff (!reset_n)
                   $past(reset_n) && $past(address != 2'b00) |-> readdata == 16'h0)
    else $error("Nonzero readdata when previous address != 0");

  // Functional coverage
  cover property (@(posedge clk) $fell(reset_n));
  cover property (@(posedge clk) $rose(reset_n));
  cover property (@(posedge clk) disable iff (!reset_n)
                  address == 2'b00 ##1 readdata == $past(in_port));
  cover property (@(posedge clk) disable iff (!reset_n)
                  address != 2'b00 ##1 readdata == 16'h0);
  cover property (@(posedge clk) disable iff (!reset_n)
                  address == 2'b00 && $changed(in_port) ##1 readdata == $past(in_port));

endmodule

bind pio_latency pio_latency_sva
(
  .clk      (clk),
  .reset_n  (reset_n),
  .address  (address),
  .in_port  (in_port),
  .readdata (readdata)
);