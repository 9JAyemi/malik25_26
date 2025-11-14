// SVA for clk_gen – bindable, concise, and high quality

module clk_gen_sva #(
  parameter int res   = 20,
  parameter int phase = 1
)(
  input  logic              clk_i,
  input  logic              rst_i,
  input  logic              clk_o,
  input  logic [res-1:0]    cnt
);

  typedef logic [res-1:0] word_t;
  localparam word_t PH = word_t'(phase);

  default clocking cb @(posedge clk_i); endclocking

  // Parameter sanity
  initial begin
    assert (res > 0) else $fatal(1, "clk_gen: res must be > 0");
    assert (phase >= 0) else $fatal(1, "clk_gen: phase must be >= 0");
  end

  // Reset behavior: next cycle zero and hold zero while asserted
  property p_rst_to_zero; rst_i |=> (cnt == '0); endproperty
  assert property (p_rst_to_zero);

  property p_rst_hold_zero; rst_i && $past(rst_i) |-> (cnt == '0); endproperty
  assert property (p_rst_hold_zero);

  // Functional increment modulo 2^res when active
  // $past(1) filters out the very first sample
  property p_inc_by_phase; disable iff (rst_i) $past(1'b1) |-> (cnt == $past(cnt) + PH); endproperty
  assert property (p_inc_by_phase);

  // Output equals MSB of counter (and not X)
  assert property (clk_o === cnt[res-1]);

  // No X on state/output when active
  assert property (disable iff (rst_i) !$isunknown({cnt, clk_o}));

  // Coverage: reset release, MSB edges, and wrap-around
  cover property ($fell(rst_i));
  cover property (disable iff (rst_i) $rose(clk_o));
  cover property (disable iff (rst_i) $fell(clk_o));
  cover property (disable iff (rst_i) $past(1'b1) && ($past(cnt) > cnt)); // wrap

endmodule

// Bind into clk_gen; connects to internal cnt
bind clk_gen clk_gen_sva #(.res(res), .phase(phase))
  clk_gen_sva_i (.clk_i(clk_i), .rst_i(rst_i), .clk_o(clk_o), .cnt(cnt));