// Bind these SVA to the DUT to check correctness and provide concise coverage.
// Focus: BCD digit validity, functional correctness, consistency, and key range coverage.

module binary_to_bcd_sva(
  input  logic [7:0]  binary,
  input  logic [11:0] bcd,
  input  logic [3:0]  digit1, digit2, digit3
);

  // Local free-running clock for sampling SVA on a stable edge
  logic sva_clk;
  initial sva_clk = 0;
  always #1 sva_clk = ~sva_clk;

  default clocking cb @(posedge sva_clk); endclocking

  // Expected digit functions (mirror DUT intent)
  function automatic logic [3:0] exp_d1 (input logic [7:0] bin);
    return (bin >= 8'd100) ? bin/8'd100 : 4'd0;
  endfunction
  function automatic logic [3:0] exp_d2 (input logic [7:0] bin);
    return (bin >= 8'd100) ? (bin%8'd100)/8'd10 :
           (bin >= 8'd10 ) ?  bin/8'd10 : 4'd0;
  endfunction
  function automatic logic [3:0] exp_d3 (input logic [7:0] bin);
    return (bin >= 8'd10) ? bin%8'd10 : bin[3:0];
  endfunction

  // Helpers
  function automatic bit known(input logic [31:0] x); return !$isunknown(x); endfunction

  // 1) Digits valid and no X/Z when input is known
  property digits_valid_p;
    ! $isunknown(binary) |-> ##0
      (! $isunknown({digit1,digit2,digit3,bcd}) &&
       (digit1 < 10) && (digit2 < 10) && (digit3 < 10));
  endproperty
  assert property (digits_valid_p) else $error("BCD digits invalid or X/Z");

  // 2) bcd output matches internal digits
  property bcd_concat_p;
    ! $isunknown(binary) |-> ##0 (bcd == {digit1, digit2, digit3});
  endproperty
  assert property (bcd_concat_p) else $error("bcd != {digit1,digit2,digit3}");

  // 3) Functional equivalence to decimal value
  property numeric_equiv_p;
    ! $isunknown(binary) |-> ##0
      (int'(digit1)*100 + int'(digit2)*10 + int'(digit3) == int'(binary));
  endproperty
  assert property (numeric_equiv_p) else $error("Numeric equivalence failed");

  // 4) Piecewise definition matches spec
  property lt10_p;
    (! $isunknown(binary) && (binary < 8'd10)) |-> ##0
      (digit1==0 && digit2==0 && digit3==binary[3:0]);
  endproperty
  assert property (lt10_p) else $error("<10 case mismatch");

  property r10_99_p;
    (! $isunknown(binary) && (binary inside {[8'd10:8'd99]})) |-> ##0
      (digit1==0 && digit2==(binary/8'd10) && digit3==(binary%8'd10));
  endproperty
  assert property (r10_99_p) else $error("10..99 case mismatch");

  property ge100_p;
    (! $isunknown(binary) && (binary >= 8'd100)) |-> ##0
      (digit1==(binary/8'd100) &&
       digit2==((binary%8'd100)/8'd10) &&
       digit3==(binary%8'd10));
  endproperty
  assert property (ge100_p) else $error(">=100 case mismatch");

  // 5) Alternative direct functional check via expected functions
  property expected_funcs_p;
    ! $isunknown(binary) |-> ##0
      (digit1==exp_d1(binary) && digit2==exp_d2(binary) && digit3==exp_d3(binary));
  endproperty
  assert property (expected_funcs_p) else $error("Expected function mapping mismatch");

  // 6) Zero-latency response on input change (combinational behavior)
  property zero_latency_p;
    $changed(binary) && ! $isunknown(binary) |-> ##0
      (bcd == {exp_d1(binary), exp_d2(binary), exp_d3(binary)});
  endproperty
  assert property (zero_latency_p) else $error("Non-combinational response detected");

  // Coverage: key ranges and boundaries
  cover property ($changed(binary) && binary == 8'd0);
  cover property ($changed(binary) && binary == 8'd9);
  cover property ($changed(binary) && binary == 8'd10);
  cover property ($changed(binary) && binary == 8'd99);
  cover property ($changed(binary) && binary == 8'd100);
  cover property ($changed(binary) && binary == 8'd255);

  // Coverage: each range exercised
  cover property ($changed(binary) && (binary < 8'd10));
  cover property ($changed(binary) && (binary inside {[8'd10:8'd99]}));
  cover property ($changed(binary) && (binary >= 8'd100));

endmodule

// Bind into the DUT
bind binary_to_bcd binary_to_bcd_sva b2bcd_sva_inst(
  .binary(binary),
  .bcd(bcd),
  .digit1(digit1),
  .digit2(digit2),
  .digit3(digit3)
);