// SVA for the given design. Bind into top_module.
// Focused, high-quality checks with essential coverage.

module top_module_sva (
  input  logic        clk,
  input  logic        rst_n,
  input  logic        a,
  input  logic        b,
  input  logic        out_comb_ff,
  input  logic [1:0]  final_output,
  input  logic        out_comb_ff_wire,
  input  logic        rising_edge_wire,
  input  logic        falling_edge_wire,
  input  logic [1:0]  edge_state
);
  // Local copies of edge_detection encodings
  localparam logic [1:0] IDLE=2'b00, RISING=2'b01, FALLING=2'b10;

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n)

  // xor_module: registered XOR behavior and no glitches between clocks
  ap_xor_pipe:   assert property (out_comb_ff_wire == $past(a ^ b));
  ap_xor_stable: assert property (@(negedge clk) $stable(out_comb_ff_wire));

  // top output matches internal wire
  ap_out_pass:   assert property (out_comb_ff == out_comb_ff_wire);

  // edge_detection: legal state encoding only (flags lack of reset/initialization)
  ap_edge_legal: assert property (edge_state inside {IDLE, RISING, FALLING});

  // edge_detection: state transition function
  ap_tr_idle0:   assert property ($past(edge_state)==IDLE   && $past(a)==1'b0 |-> edge_state==IDLE);
  ap_tr_idle1:   assert property ($past(edge_state)==IDLE   && $past(a)==1'b1 |-> edge_state==RISING);
  ap_tr_ris1:    assert property ($past(edge_state)==RISING && $past(a)==1'b1 |-> edge_state==RISING);
  ap_tr_ris0:    assert property ($past(edge_state)==RISING && $past(a)==1'b0 |-> edge_state==FALLING);
  ap_tr_fal1:    assert property ($past(edge_state)==FALLING&& $past(a)==1'b1 |-> edge_state==RISING);
  ap_tr_fal0:    assert property ($past(edge_state)==FALLING&& $past(a)==1'b0 |-> edge_state==FALLING);

  // edge_detection: outputs match state and are mutually exclusive, no glitches
  ap_out_idle:   assert property (edge_state==IDLE    |-> rising_edge_wire==1'b0 && falling_edge_wire==1'b0);
  ap_out_rise:   assert property (edge_state==RISING  |-> rising_edge_wire==1'b1 && falling_edge_wire==1'b0);
  ap_out_fall:   assert property (edge_state==FALLING |-> rising_edge_wire==1'b0 && falling_edge_wire==1'b1);
  ap_edge_mutex: assert property (!(rising_edge_wire && falling_edge_wire));
  ap_edge_stbl:  assert property (@(negedge clk) $stable(rising_edge_wire) && $stable(falling_edge_wire));

  // Edge response to input edges (1-cycle latency)
  ap_rise_det:   assert property ($rose(a) |=> rising_edge_wire);
  ap_fall_det:   assert property ($fell(a) |=> falling_edge_wire);

  // final_module: exact truth table (including priority)
  ap_final_10:   assert property ((out_comb_ff_wire && rising_edge_wire) |-> final_output==2'b10);
  ap_final_01:   assert property ((!(out_comb_ff_wire && rising_edge_wire) &&
                                   (out_comb_ff_wire || rising_edge_wire || falling_edge_wire))
                                  |-> final_output==2'b01);
  ap_final_00:   assert property ((!(out_comb_ff_wire || rising_edge_wire || falling_edge_wire))
                                  |-> final_output==2'b00);
  ap_final_no11: assert property (final_output != 2'b11);

  // Sanity: no X on key outputs during operation
  ap_no_x:       assert property (!$isunknown({out_comb_ff_wire, rising_edge_wire, falling_edge_wire, final_output}));

  // Coverage: exercise edges, states, and all final outputs
  cv_rise:       cover property ($rose(a));
  cv_fall:       cover property ($fell(a));
  cv_id:         cover property (edge_state==IDLE);
  cv_rs:         cover property (edge_state==RISING);
  cv_fl:         cover property (edge_state==FALLING);
  cv_f0:         cover property (final_output==2'b00);
  cv_f1:         cover property (final_output==2'b01);
  cv_f2:         cover property (final_output==2'b10);
  cv_prio:       cover property (out_comb_ff_wire && rising_edge_wire && final_output==2'b10);
  cv_or_only:    cover property (!out_comb_ff_wire && !rising_edge_wire && falling_edge_wire && final_output==2'b01);
endmodule

// Bind into top; capture internal edge_inst.state via a port
bind top_module top_module_sva i_top_sva (
  .clk               (clk),
  .rst_n             (rst_n),
  .a                 (a),
  .b                 (b),
  .out_comb_ff       (out_comb_ff),
  .final_output      (final_output),
  .out_comb_ff_wire  (out_comb_ff_wire),
  .rising_edge_wire  (rising_edge_wire),
  .falling_edge_wire (falling_edge_wire),
  .edge_state        (edge_inst.state)
)