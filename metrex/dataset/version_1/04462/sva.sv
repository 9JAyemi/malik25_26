// Bindable SVA checker for top_module
module top_module_sva;

  // Access DUT scope signals via bind
  // DUT has: a,b, lt,eq,gt, seg_a,seg_b, bcd_a,bcd_b

  // 7-seg decode function (must match DUT truth table)
  function automatic [6:0] decode7seg (input logic [3:0] d);
    case (d)
      4'd0: decode7seg = 7'b1000000;
      4'd1: decode7seg = 7'b1111001;
      4'd2: decode7seg = 7'b0100100;
      4'd3: decode7seg = 7'b0110000;
      4'd4: decode7seg = 7'b0011001;
      4'd5: decode7seg = 7'b0010010;
      4'd6: decode7seg = 7'b0000010;
      4'd7: decode7seg = 7'b1111000;
      4'd8: decode7seg = 7'b0000000;
      4'd9: decode7seg = 7'b0010000;
      default: decode7seg = 7'b1111111;
    endcase
  endfunction

  // Sensitivity: sample on any relevant comb change
  localparam bit ZERO = 1'b0;

  // Outputs must never go X/Z when inputs are known
  ap_no_x: assert property (@(a or b or lt or eq or gt or seg_a or seg_b or bcd_a or bcd_b)
                            (!$isunknown({a,b})) |-> !$isunknown({lt,eq,gt,seg_a,seg_b}));

  // Comparator correctness and exclusivity
  ap_cmp_map: assert property (@(a or b or lt or eq or gt)
                               (!$isunknown({a,b})) |-> ((lt == (a < b)) && (eq == (a == b)) && (gt == (a > b))));
  ap_cmp_onehot: assert property (@(a or b or lt or eq or gt)
                                  (!$isunknown({lt,eq,gt})) |-> $onehot({lt,eq,gt}));

  // BCD nibbles mapping as coded in DUT (note: a is ignored by DUT assign/truncation)
  ap_bcd_map: assert property (@(a or b or bcd_a or bcd_b)
                               (!$isunknown(b)) |-> ((bcd_a == b[7:4]) && (bcd_b == b[3:0])));

  // 7-seg decoders must match spec for both channels
  ap_seg_a: assert property (@(bcd_a or seg_a)
                             (!$isunknown(bcd_a)) |-> (seg_a == decode7seg(bcd_a)));
  ap_seg_b: assert property (@(bcd_b or seg_b)
                             (!$isunknown(bcd_b)) |-> (seg_b == decode7seg(bcd_b)));

  // Invalid BCD (10..15) must produce 7'b1111111
  ap_inv_a: assert property (@(bcd_a or seg_a)
                             (!$isunknown(bcd_a) && (bcd_a > 4'd9)) |-> (seg_a == 7'b1111111));
  ap_inv_b: assert property (@(bcd_b or seg_b)
                             (!$isunknown(bcd_b) && (bcd_b > 4'd9)) |-> (seg_b == 7'b1111111));

  // Minimal but meaningful coverage
  cp_lt:  cover property (@(a or b) ((a < b)  && lt));
  cp_eq:  cover property (@(a or b) ((a == b) && eq));
  cp_gt:  cover property (@(a or b) ((a > b)  && gt));

  cp_a_digit0: cover property (@(bcd_a or seg_a) (bcd_a == 4'd0) && (seg_a == decode7seg(4'd0)));
  cp_a_digit9: cover property (@(bcd_a or seg_a) (bcd_a == 4'd9) && (seg_a == decode7seg(4'd9)));
  cp_a_inv:    cover property (@(bcd_a or seg_a) (bcd_a >  4'd9) && (seg_a == 7'b1111111));

  cp_b_digit0: cover property (@(bcd_b or seg_b) (bcd_b == 4'd0) && (seg_b == decode7seg(4'd0)));
  cp_b_digit9: cover property (@(bcd_b or seg_b) (bcd_b == 4'd9) && (seg_b == decode7seg(4'd9)));
  cp_b_inv:    cover property (@(bcd_b or seg_b) (bcd_b >  4'd9) && (seg_b == 7'b1111111));

endmodule

// Bind into DUT
bind top_module top_module_sva sva_top_module();