// SVA for cclk_detector
// Bindable, concise, and checks the full next-state function plus key invariants and coverage.

`ifndef CCLK_DETECTOR_SVA
`define CCLK_DETECTOR_SVA

module cclk_detector_sva #(
  parameter int CLK_RATE = 50000000
)(
  input  logic clk,
  input  logic rst,
  input  logic cclk,
  input  logic ready,
  input  logic [$clog2(CLK_RATE/50000)-1:0] ctr_q,
  input  logic ready_q
);

  localparam int CTR_SIZE_P = $clog2(CLK_RATE/50000);
  localparam int MAX_I      = (1 << CTR_SIZE_P) - 1;
  localparam logic [CTR_SIZE_P-1:0] MAX = {CTR_SIZE_P{1'b1}};

  default clocking cb @(posedge clk); endclocking

  // Next-state functional correctness (single-cycle, covers reset, count, hold, clear)
  property p_next_ready;
    1 |=> (ready_q == (rst ? 1'b0 : ($past(cclk) && ($past(ctr_q) == MAX))));
  endproperty
  a_next_ready: assert property (p_next_ready);

  property p_next_ctr;
    1 |=> (ctr_q == (rst ? '0 : ($past(cclk) ? (($past(ctr_q) == MAX) ? $past(ctr_q) : ($past(ctr_q) + 1)) : '0)));
  endproperty
  a_next_ctr: assert property (p_next_ctr);

  // Invariants
  a_ready_is_reg:    assert property (ready == ready_q);
  a_no_overflow:     assert property (ctr_q <= MAX);
  a_ready_implies_prev_sat: assert property (ready_q |-> ($past(cclk) && ($past(ctr_q) == MAX)));

  // Covers: increment path, saturation, clear, and end-to-end run-to-ready
  c_inc:      cover property (disable iff (rst) (cclk && (ctr_q != MAX)) ##1 (ctr_q == $past(ctr_q) + 1));
  c_sat:      cover property (disable iff (rst) (cclk && (ctr_q == MAX)) ##1 (ready_q && (ctr_q == MAX)));
  c_clear:    cover property (disable iff (rst) (!cclk) ##1 (ctr_q == '0 && !ready_q));
  c_ready_rise:cover property ($rose(ready));
  c_run2ready: cover property (disable iff (rst) cclk [* (MAX_I+1)] ##1 ready_q);

endmodule

// Example bind (connects to internal regs ctr_q, ready_q)
bind cclk_detector cclk_detector_sva #(.CLK_RATE(CLK_RATE)) cclk_detector_sva_i (
  .clk    (clk),
  .rst    (rst),
  .cclk   (cclk),
  .ready  (ready),
  .ctr_q  (ctr_q),
  .ready_q(ready_q)
);

`endif