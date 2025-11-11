// SVA checker for decoder_4to16
// Bind to DUT and hook a clock/reset for temporal checks and coverage.
// Immediate checks fire without a clock.

module decoder_4to16_sva (
  input  logic        clk,
  input  logic        rst_n,
  input  logic        enable,
  input  logic [3:0]  select,
  input  logic [15:0] out
);

  function automatic logic [15:0] exp_decode (logic en, logic [3:0] sel);
    return en ? (16'h1 << sel) : 16'h0;
  endfunction

  // Clockless immediate checks (combinational correctness, one-hot, knownness)
  always_comb begin
    if (!$isunknown({enable, select})) begin
      assert (out == exp_decode(enable, select))
        else $error("decoder_4to16 mismatch: en=%0b sel=%0h out=%0h", enable, select, out);
      assert (!$isunknown(out))
        else $error("decoder_4to16 out has X/Z with known inputs");
      assert ($onehot0(out))
        else $error("decoder_4to16 out is not onehot0");
      if (enable) begin
        assert ($onehot(out))
          else $error("decoder_4to16 out not exactly one-hot when enable=1");
      end else begin
        assert (out == 16'h0)
          else $error("decoder_4to16 out not zero when enable=0");
      end
    end
  end

  // Clocked temporal checks and coverage
  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Stability: if inputs don’t change, outputs don’t change
  assert property ( $stable({enable, select}) |-> $stable(out) );

  // Functional cover: hit all selects when enabled, and disable case
  genvar i;
  generate
    for (i = 0; i < 16; i++) begin : g_cov
      cover property ( enable && select == i[3:0] && out[i] );
    end
  endgenerate
  cover property ( !enable && out == 16'h0 );

endmodule

// Example bind (provide a clock/reset from TB)
// bind decoder_4to16 decoder_4to16_sva u_dec_sva(.clk(tb_clk), .rst_n(1'b1), .enable(enable), .select(select), .out(out));