// SVA for iddr: checks DDR capture semantics concisely
// Bind into the DUT type "iddr"
`ifndef SYNTHESIS

module iddr_sva #(parameter int WIDTH = 1)
(
  input  wire             clk,
  input  wire [WIDTH-1:0] d,
  input  wire [WIDTH-1:0] q1,
  input  wire [WIDTH-1:0] q2
);

  // Basic parameter sanity
  initial if (WIDTH <= 0) $error("iddr_sva: WIDTH must be > 0");

  // Shadow samples of d at both edges
  logic [WIDTH-1:0] d_pos, d_neg;
  logic pos_seen, neg_seen, init_done;

  always @(posedge clk) begin
    d_pos    <= d;
    pos_seen <= 1'b1;
    init_done <= pos_seen & neg_seen;
  end

  always @(negedge clk) begin
    d_neg    <= d;
    neg_seen <= 1'b1;
  end

  // q1 equals previous posedge sample of d (one posedge latency)
  property p_q1_prev_posedge;
    @(posedge clk) pos_seen && $past(pos_seen) |-> (q1 == $past(d_pos));
  endproperty
  a_q1_prev_posedge: assert property (p_q1_prev_posedge);

  // q2 equals most recent negedge sample of d (immediately preceding this posedge)
  property p_q2_last_negedge;
    @(posedge clk) neg_seen |-> (q2 == d_neg);
  endproperty
  a_q2_last_negedge: assert property (p_q2_last_negedge);

  // Outputs must not change on negedge (both are posedge-aligned)
  a_no_change_on_negedge: assert property (@(negedge clk) $stable({q1,q2}));

  // No X/Z on outputs once both edges have been observed
  a_no_x_after_init: assert property (@(posedge clk) init_done |-> !$isunknown({q1,q2}));

  // Coverage: observe both phase transfers with actual data changes
  c_posedge_path:  cover property (@(posedge clk) pos_seen && $changed(d_pos) && (q1 == $past(d_pos)));
  c_negedge_path:  cover property (@(posedge clk) neg_seen && $changed(d_neg) && (q2 == d_neg));

endmodule

bind iddr iddr_sva #(.WIDTH(WIDTH)) iddr_sva_i (.*);

`endif