// SVA for start_for_CvtColowdI_shiftReg
// Bindable checker with compact reference model and key properties

module start_for_CvtColowdI_shiftReg_sva #(
  parameter int DATA_WIDTH = 1,
  parameter int ADDR_WIDTH = 2,
  parameter int DEPTH      = 3
)(
  input  logic                     clk,
  input  logic [DATA_WIDTH-1:0]    data,
  input  logic                     ce,
  input  logic [ADDR_WIDTH-1:0]    a,
  input  logic [DATA_WIDTH-1:0]    q
);

  default clocking cb @(posedge clk); endclocking

  // Reference model (mirrors DUT behavior using only ports)
  logic [DATA_WIDTH-1:0] ref [0:DEPTH-1];
  logic [DEPTH-1:0]      val_vec; // validity of each stage; packed for easy indexing/reduction
  integer i;

  always_ff @(posedge clk) begin
    if (ce) begin
      for (i = DEPTH-1; i > 0; i = i-1) begin
        ref[i] <= ref[i-1];
      end
      ref[0]   <= data;
      val_vec  <= {val_vec[DEPTH-2:0], !$isunknown(data)}; // stage valid only if input known
    end
  end

  // Basic sanity
  a_ce_known:        assert property (!$isunknown(ce));
  a_a_in_range:      assert property (a < DEPTH);

  // Functional correctness: q must equal selected tap of the reference model when that tap is valid
  a_q_matches_ref:   assert property ((a < DEPTH) && val_vec[a] |-> q == ref[a]);

  // No X leakage on q when selecting a valid tap
  a_q_not_x_when_valid: assert property ((a < DEPTH) && val_vec[a] |-> !$isunknown(q));

  // Hold behavior: if ce=0 and address stable, q must be stable
  a_hold_when_ce0_and_a_stable: assert property ((!ce && $stable(a)) |-> $stable(q));

  // Valid vector must not change when ce=0
  a_val_hold_when_ce0: assert property ((!ce) |-> $stable(val_vec));

  // Coverage
  c_seen_write:           cover property (ce && !$isunknown(data));
  c_full_pipeline_valid:  cover property (&val_vec);
  c_addr0_tap_used:       cover property ((&val_vec) && a == '0);
  c_addr_last_tap_used:   cover property ((&val_vec) && a == (DEPTH-1));
  c_shift_changes_q:      cover property ((&val_vec) && $stable(a) && $rose(ce) ##1 $changed(q));

endmodule

bind start_for_CvtColowdI_shiftReg
  start_for_CvtColowdI_shiftReg_sva #(
    .DATA_WIDTH(DATA_WIDTH),
    .ADDR_WIDTH(ADDR_WIDTH),
    .DEPTH     (DEPTH)
  ) u_start_for_CvtColowdI_shiftReg_sva (
    .clk (clk),
    .data(data),
    .ce  (ce),
    .a   (a),
    .q   (q)
  );