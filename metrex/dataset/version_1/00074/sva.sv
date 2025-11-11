// SVA: bindable checker for top_module

module top_module_sva
(
  input logic         clk,
  input logic         reset,
  input logic         slowena,
  input logic [31:0]  in,
  input logic [31:0]  byte_reversed,
  input logic [31:0]  out,
  input logic [3:0]   counter
);
  default clocking cb @(posedge clk); endclocking

  // Basic X/Z checks
  assert property (@(posedge clk) !$isunknown(reset)) else $error("reset is X/Z");
  assert property (disable iff (!reset) !$isunknown({slowena,in,byte_reversed,out,counter}))
    else $error("X/Z on active signals");

  // Byte reverse correctness
  assert property (byte_reversed == {in[7:0], in[15:8], in[23:16], in[31:24]})
    else $error("byte_reverse mapping mismatch");

  // Adder correctness
  assert property (out == byte_reversed + counter)
    else $error("adder output mismatch");

  // Counter: asynchronous reset behavior
  assert property (@(negedge reset) counter == 4'h0)
    else $error("counter not 0 on negedge reset");
  assert property (!reset |-> counter == 4'h0)
    else $error("counter nonzero while reset low");

  // Counter: hold when slowena==0
  assert property (reset && !slowena |-> $stable(counter))
    else $error("counter changed while slowena=0");

  // Counter: increment by 1 modulo 16 when slowena==1
  assert property (reset && slowena |=> counter == (($past(counter)+1) & 4'hF))
    else $error("counter did not increment by 1 mod 16");

  // Functional coverage
  cover property ($rose(reset));
  cover property (reset && !slowena ##1 counter == $past(counter));                  // hold observed
  cover property (reset && slowena ##1 counter == (($past(counter)+1) & 4'hF));      // increment observed
  cover property (reset && slowena && counter==4'hF |=> counter==4'h0);              // wrap-around observed
  cover property (reset && ((byte_reversed[3:0] + counter) >= 5'd16));               // low-nibble carry into bit[4]
  cover property (in==32'hA1B2C3D4 && byte_reversed==32'hD4C3B2A1);                  // exemplar byte swap seen
endmodule

bind top_module top_module_sva u_top_module_sva
(
  .clk(clk),
  .reset(reset),
  .slowena(slowena),
  .in(in),
  .byte_reversed(byte_reversed),
  .out(out),
  .counter(counter)
);