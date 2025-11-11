// SVA checker for SevenSegmentLED
// - Asserts decode correctness and X-free outputs for known inputs
// - Covers all 16 input codes and both 0/1 on each segment
// Bind this checker to the DUT.

module SevenSegmentLED_sva(
  input  logic [3:0] i_data,
  input  logic       o_a,
  input  logic       o_b,
  input  logic       o_c,
  input  logic       o_d,
  input  logic       o_e,
  input  logic       o_f,
  input  logic       o_g
);

  // Expected decode table: bit [6] -> a ... bit [0] -> g (active-low patterns as in DUT)
  localparam logic [6:0] TBL [0:15] = '{
    7'b0000001, // 0
    7'b1001111, // 1
    7'b0010010, // 2
    7'b0000110, // 3
    7'b1001100, // 4
    7'b0100100, // 5
    7'b0100000, // 6
    7'b0001111, // 7
    7'b0000000, // 8
    7'b0000100, // 9
    7'b0001000, // A
    7'b1100000, // b
    7'b0110001, // C
    7'b1000010, // d
    7'b0110000, // E
    7'b0111000  // F
  };

  // Static sanity: all patterns unique
  initial begin
    for (int i = 0; i < 16; i++) begin
      for (int j = i+1; j < 16; j++) begin
        assert (TBL[i] !== TBL[j])
          else $error("SevenSegmentLED_sva: duplicate pattern for %0h and %0h", i, j);
      end
    end
  end

  // Combinational assertions and coverage
  always_comb begin
    logic [6:0] out = {o_a,o_b,o_c,o_d,o_e,o_f,o_g};

    // Valid inputs must produce the exact expected code and no X/Z on outputs
    if (!$isunknown(i_data)) begin
      assert (out === TBL[i_data])
        else $error("SevenSegmentLED_sva: decode mismatch: i_data=%0h out=%b exp=%b",
                    i_data, out, TBL[i_data]);
      assert (!$isunknown(out))
        else $error("SevenSegmentLED_sva: X/Z detected on outputs for i_data=%0h", i_data);
    end

    // Outputs must always be 7-state binary (no X/Z) if any output bit is known active-low style
    // (Optional strictness: comment out if you expect X-propagation when inputs are X)
    // if ($isunknown(i_data)) assert ($isunknown(out) || !$isunknown(out));

    // Functional coverage: exercise all 16 inputs
    for (int k = 0; k < 16; k++) begin
      cover (i_data == k[3:0]);
    end

    // Functional coverage: see each output bit as 0 and 1 at least once
    cover (o_a == 1'b0); cover (o_a == 1'b1);
    cover (o_b == 1'b0); cover (o_b == 1'b1);
    cover (o_c == 1'b0); cover (o_c == 1'b1);
    cover (o_d == 1'b0); cover (o_d == 1'b1);
    cover (o_e == 1'b0); cover (o_e == 1'b1);
    cover (o_f == 1'b0); cover (o_f == 1'b1);
    cover (o_g == 1'b0); cover (o_g == 1'b1);

    // Functional coverage: confirm only legal patterns are produced
    if (!$isunknown(out)) begin
      bit legal = 1'b0;
      for (int v = 0; v < 16; v++) legal |= (out === TBL[v]);
      cover (legal);
      assert (legal)
        else $error("SevenSegmentLED_sva: illegal 7-seg pattern observed: %b", out);
    end
  end

endmodule

// Bind into DUT
bind SevenSegmentLED SevenSegmentLED_sva u_sevenseg_sva (
  .i_data(i_data),
  .o_a(o_a), .o_b(o_b), .o_c(o_c), .o_d(o_d), .o_e(o_e), .o_f(o_f), .o_g(o_g)
);