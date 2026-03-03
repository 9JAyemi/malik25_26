// SVA for BIN_DEC2: binary(16) -> BCD(5 nibbles)
// Bind this module to BIN_DEC2; provide a sampling clock if you want concurrent cover.
// Otherwise, immediate assertions run combinationally.

module BIN_DEC2_sva
(
  input  logic [15:0] B2,
  input  logic [19:0] bcdout2
`ifdef ASSERT_CLK
 ,input  logic        clk
`endif
);

  // Reference conversion: binary -> packed BCD {d4,d3,d2,d1,d0}
  function automatic logic [19:0] bcd_ref(input logic [15:0] b);
    int unsigned t;
    logic [3:0] d0,d1,d2,d3,d4;
    t  = b;
    d0 = t % 10; t = t / 10;
    d1 = t % 10; t = t / 10;
    d2 = t % 10; t = t / 10;
    d3 = t % 10; t = t / 10;
    d4 = t % 10;
    return {d4,d3,d2,d1,d0};
  endfunction

  // Packed BCD -> integer value (for cross-check)
  function automatic int unsigned bcd_to_bin(input logic [19:0] bcd);
    return (10000*bcd[19:16]) + (1000*bcd[15:12]) + (100*bcd[11:8]) + (10*bcd[7:4]) + bcd[3:0];
  endfunction

  // Nibble aliases
  wire [3:0] d4 = bcdout2[19:16];
  wire [3:0] d3 = bcdout2[15:12];
  wire [3:0] d2 = bcdout2[11:8];
  wire [3:0] d1 = bcdout2[7:4];
  wire [3:0] d0 = bcdout2[3:0];

  // Immediate (combinational) assertions
  always_comb begin
    // No X/Z on input implies no X/Z on output and valid BCD digits
    if (!$isunknown(B2)) begin
      assert (!$isunknown(bcdout2))
        else $error("BIN_DEC2: X/Z detected on bcdout2 for B2=%0d", B2);

      assert (d0<=9 && d1<=9 && d2<=9 && d3<=9 && d4<=9)
        else $error("BIN_DEC2: Non-BCD digit in bcdout2=%h for B2=%0d", bcdout2, B2);

      // Functional equivalence (both directions)
      assert (bcdout2 === bcd_ref(B2))
        else $error("BIN_DEC2: Output mismatch. B2=%0d expected BCD=%h got %h", B2, bcd_ref(B2), bcdout2);

      assert (bcd_to_bin(bcdout2) == B2)
        else $error("BIN_DEC2: BCD decodes to %0d, expected %0d. bcdout2=%h", bcd_to_bin(bcdout2), B2, bcdout2);
    end
  end

  // Concise but targeted coverage
`ifdef ASSERT_CLK
  default clocking cb @(posedge clk); endclocking
  cover property (B2==16'd0    && bcdout2==20'h00000);
  cover property (B2==16'd9    && bcdout2==20'h00009);
  cover property (B2==16'd10   && bcdout2==20'h00010);
  cover property (B2==16'd15   && bcdout2==20'h00015);
  cover property (B2==16'd99   && bcdout2==20'h00099);
  cover property (B2==16'd100  && bcdout2==20'h00100);
  cover property (B2==16'd255  && bcdout2==20'h00255);
  cover property (B2==16'd4095 && bcdout2==20'h04095);
  cover property (B2==16'd32768&& bcdout2==20'h32768);
  cover property (B2==16'd65535&& bcdout2==20'h65535);
`else
  // Immediate coverage (if no clock provided)
  always_comb begin
    cover (B2==16'd0    && bcdout2==20'h00000);
    cover (B2==16'd9    && bcdout2==20'h00009);
    cover (B2==16'd10   && bcdout2==20'h00010);
    cover (B2==16'd15   && bcdout2==20'h00015);
    cover (B2==16'd99   && bcdout2==20'h00099);
    cover (B2==16'd100  && bcdout2==20'h00100);
    cover (B2==16'd255  && bcdout2==20'h00255);
    cover (B2==16'd4095 && bcdout2==20'h04095);
    cover (B2==16'd32768&& bcdout2==20'h32768);
    cover (B2==16'd65535&& bcdout2==20'h65535);
  end
`endif

endmodule

// Bind template (connect clk if you want concurrent cover):
// bind BIN_DEC2 BIN_DEC2_sva u_BIN_DEC2_sva(.B2(B2), .bcdout2(bcdout2) /*, .clk(tb_clk)*/);