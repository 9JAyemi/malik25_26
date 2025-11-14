// SVA bind module for squarer: concise, full bit-coverage and functional checks
module squarer_sva (input logic [232:0] a, input logic [232:0] d);

  // Combinational, clockless checks and coverage
  always_comb begin
    // Stimulus/observability coverage on all inputs/outputs (both 0 and 1 seen)
    for (int i = 0; i <= 232; i++) begin
      cover (a[i] == 1'b0);
      cover (a[i] == 1'b1);
      cover (d[i] == 1'b0);
      cover (d[i] == 1'b1);
    end

    if (!$isunknown(a)) begin
      // Region d[0..73]
      for (int k = 0; k <= 36; k++) begin
        assert #0 (d[2*k]   === (a[k] ^ a[196+k])) else $error("d[%0d] mismatch", 2*k);
        assert #0 (d[2*k+1] ===  a[117+k])         else $error("d[%0d] mismatch", 2*k+1);
      end

      // Region d[74..147]
      for (int k = 0; k <= 36; k++) begin
        assert #0 (d[74 + 2*k] === (a[37+k]  ^ a[196+k])) else $error("d[%0d] mismatch", 74+2*k);
        assert #0 (d[75 + 2*k] === (a[117+k] ^ a[154+k])) else $error("d[%0d] mismatch", 75+2*k);
      end

      // Region d[148..232] even: pass-through a[74..116]
      for (int k = 0; k <= 42; k++) begin
        assert #0 (d[148 + 2*k] === a[74+k]) else $error("d[%0d] mismatch", 148+2*k);
      end

      // Region d[149..231] odd: XOR a[154..195] ^ a[191..232]
      for (int k = 0; k <= 41; k++) begin
        assert #0 (d[149 + 2*k] === (a[154+k] ^ a[191+k])) else $error("d[%0d] mismatch", 149+2*k);
      end

      // No X/Z on outputs when inputs are clean
      assert #0 (!$isunknown(d)) else $error("Unknown on d with known a");
    end
  end

endmodule

bind squarer squarer_sva sva (.a(a), .d(d));