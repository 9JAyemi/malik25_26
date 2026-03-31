```systemverilog
module address_to_signal_sva (
  input logic [9:0] address,
  input logic clock,
  output logic [11:0] q
);
  // Sequential logic behavior: q is inverted on the rising edge of the clock
  sequential_logic: assert property (
    @(posedge clock) $stable(address) |-> q == ~{address, 2'b00}
  );

  // Combinational logic behavior: q is shifted left by 2 bits
  combinational_logic: assert property (
    @(posedge clock) $stable(address) |-> q == {address, 2'b00}
  );
endmodule
```