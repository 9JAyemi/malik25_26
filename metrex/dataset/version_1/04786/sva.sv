// Bindable SVA for cf_csc_1_mul
// Checks: latency, functional equivalence, pipeline, Booth recoding, and basic coverage.
module cf_csc_1_mul_sva;

  // Use DUT scope signals directly via bind
  // default clock
  default clocking cb @(posedge clk); endclocking

  localparam int LAT = 3;

  // simple past-valid guard for deep $past
  logic [2:0] past_cnt;
  logic       past_ok;
  always_ff @(posedge clk) begin
    past_cnt <= (past_cnt == LAT) ? past_cnt : past_cnt + 1;
    past_ok  <= (past_cnt == LAT);
  end

  // helper: unsigned 16x8 => 24-bit
  function automatic logic [23:0] umul24(logic [15:0] a16, logic [7:0] b8);
    umul24 = $unsigned(a16) * $unsigned(b8);
  endfunction

  // Top-level functional checks (3-cycle latency)
  assert property (disable iff (!past_ok)
                   data_p[24] == $past(data_a[16], LAT))
    else $error("Sign latency mismatch");

  assert property (disable iff (!past_ok)
                   data_p[23:0] == $past(umul24(data_a[15:0], data_b), LAT))
    else $error("Magnitude multiply mismatch");

  assert property (disable iff (!past_ok)
                   ddata_out == $past(ddata_in, LAT))
    else $error("Delay data latency mismatch");

  // No X on outputs after pipeline fills
  assert property (disable iff (!past_ok)
                   !$isunknown(data_p) && !$isunknown(ddata_out))
    else $error("Unknown detected on outputs");

  // Pipeline consistency
  assert property (p2_sign      == $past(p1_sign))
    else $error("p2_sign != $past(p1_sign)");
  assert property (p3_sign      == $past(p2_sign))
    else $error("p3_sign != $past(p2_sign)");
  assert property (p2_ddata     == $past(p1_ddata))
    else $error("p2_ddata != $past(p1_ddata)");
  assert property (p3_ddata     == $past(p2_ddata))
    else $error("p3_ddata != $past(p2_ddata)");

  assert property (p2_data_p_0  == $past(p1_data_p_0 + p1_data_p_1 + p1_data_p_4))
    else $error("p2_data_p_0 sum mismatch");
  assert property (p2_data_p_1  == $past(p1_data_p_2 + p1_data_p_3))
    else $error("p2_data_p_1 sum mismatch");
  assert property (p3_data_p_0  == $past(p2_data_p_0 + p2_data_p_1))
    else $error("p3_data_p_0 sum mismatch");

  assert property (data_p       == {p3_sign, p3_data_p_0})
    else $error("Output pack mismatch");
  assert property (ddata_out    == p3_ddata)
    else $error("ddata_out != p3_ddata");

  // Booth recoding correctness for each partial (p1 stage)
  // LSB window [1:0]
  assert property (data_b[1:0] == 2'b00 |-> p1_data_p_0 == 24'd0);
  assert property (data_b[1:0] == 2'b01 |-> p1_data_p_0 == p1_data_a_1p_s);
  assert property (data_b[1:0] == 2'b10 |-> p1_data_p_0 == p1_data_a_2n_s);
  assert property (data_b[1:0] == 2'b11 |-> p1_data_p_0 == p1_data_a_1n_s);

  // Window [3:1], shift by 2
  assert property (data_b[3:1] == 3'b011 |-> p1_data_p_1 == {p1_data_a_2p_s[21:0], 2'd0});
  assert property (data_b[3:1] == 3'b100 |-> p1_data_p_1 == {p1_data_a_2n_s[21:0], 2'd0});
  assert property (data_b[3:1] inside {3'b001,3'b010} |-> p1_data_p_1 == {p1_data_a_1p_s[21:0], 2'd0});
  assert property (data_b[3:1] inside {3'b101,3'b110} |-> p1_data_p_1 == {p1_data_a_1n_s[21:0], 2'd0});
  assert property (data_b[3:1] inside {3'b000,3'b111} |-> p1_data_p_1 == 24'd0);

  // Window [5:3], shift by 4
  assert property (data_b[5:3] == 3'b011 |-> p1_data_p_2 == {p1_data_a_2p_s[19:0], 4'd0});
  assert property (data_b[5:3] == 3'b100 |-> p1_data_p_2 == {p1_data_a_2n_s[19:0], 4'd0});
  assert property (data_b[5:3] inside {3'b001,3'b010} |-> p1_data_p_2 == {p1_data_a_1p_s[19:0], 4'd0});
  assert property (data_b[5:3] inside {3'b101,3'b110} |-> p1_data_p_2 == {p1_data_a_1n_s[19:0], 4'd0});
  assert property (data_b[5:3] inside {3'b000,3'b111} |-> p1_data_p_2 == 24'd0);

  // Window [7:5], shift by 6
  assert property (data_b[7:5] == 3'b011 |-> p1_data_p_3 == {p1_data_a_2p_s[17:0], 6'd0});
  assert property (data_b[7:5] == 3'b100 |-> p1_data_p_3 == {p1_data_a_2n_s[17:0], 6'd0});
  assert property (data_b[7:5] inside {3'b001,3'b010} |-> p1_data_p_3 == {p1_data_a_1p_s[17:0], 6'd0});
  assert property (data_b[7:5] inside {3'b101,3'b110} |-> p1_data_p_3 == {p1_data_a_1n_s[17:0], 6'd0});
  assert property (data_b[7:5] inside {3'b000,3'b111} |-> p1_data_p_3 == 24'd0);

  // MSB correction term
  assert property (data_b[7] == 1'b1 |-> p1_data_p_4 == {p1_data_a_1p_s[15:0], 8'd0});
  assert property (data_b[7] == 1'b0 |-> p1_data_p_4 == 24'd0);

  // Coverage
  cover property (past_ok && data_p[23:0] == $past(umul24(16'd0, data_b), LAT));            // zero A
  cover property (past_ok && data_p[23:0] == $past(umul24(data_a[15:0], 8'd0), LAT));       // zero B
  cover property (past_ok && data_p[23:0] == $past(umul24(16'hFFFF, 8'hFF), LAT));          // max*max
  cover property (past_ok && data_p[24] == 1'b0);
  cover property (past_ok && data_p[24] == 1'b1);

  cover property (data_b[1:0] == 2'b01);
  cover property (data_b[1:0] == 2'b10);
  cover property (data_b[1:0] == 2'b11);
  cover property (data_b[3:1] == 3'b011);
  cover property (data_b[3:1] == 3'b100);
  cover property (data_b[3:1] == 3'b101);
  cover property (data_b[5:3] == 3'b011);
  cover property (data_b[5:3] == 3'b100);
  cover property (data_b[5:3] == 3'b101);
  cover property (data_b[7:5] == 3'b011);
  cover property (data_b[7:5] == 3'b100);
  cover property (data_b[7:5] == 3'b101);
  cover property (data_b[7] == 1'b1);

endmodule

// Bind into DUT
bind cf_csc_1_mul cf_csc_1_mul_sva i_cf_csc_1_mul_sva();