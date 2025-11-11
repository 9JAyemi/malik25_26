// SVA for and_display_module
// Bind into the DUT to see internal signals
module and_display_module_sva();

  // Clocking for concurrent assertions
  default clocking cb @(posedge clk); endclocking

  // Helper: seven-seg golden model
  function automatic [6:0] seg_map (input logic [3:0] v);
    case (v)
      4'b0000: seg_map = 7'b1000000; // 0
      4'b0001: seg_map = 7'b1111001; // 1
      4'b0010: seg_map = 7'b0100100; // 2
      4'b0011: seg_map = 7'b0110000; // 3
      4'b0100: seg_map = 7'b0011001; // 4
      4'b0101: seg_map = 7'b0010010; // 5
      4'b0110: seg_map = 7'b0000010; // 6
      4'b0111: seg_map = 7'b1111000; // 7
      4'b1000: seg_map = 7'b0000000; // 8
      4'b1001: seg_map = 7'b0011000; // 9
      default: seg_map = 7'b1111111; // off
    endcase
  endfunction

  // Local expression for the seven-seg input
  let seg_in = (and_out & logical_and_out);

  // Functional correctness
  ap_bitwise_and:      assert property (and_out == (a & b));
  ap_logical_and_wext: assert property (logical_and_out == {3'b000, ((a != 0) && (b != 0))});
  ap_not_a:            assert property (not_a_out == ~a);
  ap_not_b:            assert property (not_b_out == ~b);
  ap_out_not_concat:   assert property (out_not == {not_a_out, not_b_out});
  ap_out_not_direct:   assert property (out_not == {~a, ~b});

  // Seven-seg input reachability and decode correctness
  ap_seg_in_range:     assert property (seg_in inside {4'h0, 4'h1});
  ap_seg_decode:       assert property (seg_out == seg_map(seg_in));

  // X-propagation: if inputs known, all derived signals must be known
  ap_known: assert property (
    !$isunknown({a,b}) |-> !$isunknown({and_out, logical_and_out, not_a_out, not_b_out, seg_out, out_not})
  );

  // Coverage
  // Hit cases where seven-seg shows 0 and 1
  cv_seg_0: cover property (seg_in == 4'h0 && seg_out == 7'b1000000);
  cv_seg_1: cover property (seg_in == 4'h1 && seg_out == 7'b1111001);

  // Exercise logical-and true and false paths
  cv_logic_and_true:  cover property ((a != 0) && (b != 0) && logical_and_out == 4'b0001);
  cv_logic_and_false: cover property ((a == 0) || (b == 0) && logical_and_out == 4'b0000);

  // Bitwise AND LSB affects seg_in
  cv_and_lsb_0: cover property ((a[0] & b[0]) == 1'b0 && seg_in == 4'h0);
  cv_and_lsb_1: cover property ((a != 0) && (b != 0) && (a[0] & b[0]) == 1'b1 && seg_in == 4'h1);

  // NOT extremes
  cv_out_not_all_ones: cover property (a == 4'h0 && b == 4'h0 && out_not == 8'hFF);
  cv_out_not_all_zeros: cover property (a == 4'hF && b == 4'hF && out_not == 8'h00);

endmodule

bind and_display_module and_display_module_sva sva_and_display_module();