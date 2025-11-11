// SVA for seg7 + end-to-end decode checking (concise, quality-focused)
module seg7_assert
  #(parameter COUNTER_WIDTH = 18)
  (input  logic                       clk,
   input  logic                       reset,
   input  logic [COUNTER_WIDTH-1:0]   counter,
   input  logic                       counter_msb_d1,
   input  logic                       counter_edge,
   input  logic [1:0]                 digit,
   input  logic [15:0]                value,
   input  logic [6:0]                 seg,
   input  logic                       dp,
   input  logic [3:0]                 an,
   input  logic [6:0]                 seg0, seg1, seg2, seg3);

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // 7-seg decoder function (end-to-end check of val2seg mapping)
  function automatic logic [6:0] hex2seg (input logic [3:0] v);
    case (v)
      4'h0: hex2seg = 7'b1000000;
      4'h1: hex2seg = 7'b1111001;
      4'h2: hex2seg = 7'b0100100;
      4'h3: hex2seg = 7'b0110000;
      4'h4: hex2seg = 7'b0011001;
      4'h5: hex2seg = 7'b0010010;
      4'h6: hex2seg = 7'b0000010;
      4'h7: hex2seg = 7'b1111000;
      4'h8: hex2seg = 7'b0000000;
      4'h9: hex2seg = 7'b0010000;
      4'hA: hex2seg = 7'b0001000;
      4'hB: hex2seg = 7'b0000011;
      4'hC: hex2seg = 7'b1000110;
      4'hD: hex2seg = 7'b0100001;
      4'hE: hex2seg = 7'b0000110;
      4'hF: hex2seg = 7'b0001110;
      default: hex2seg = 7'b1111111;
    endcase
  endfunction

  // Reset state checks (override default disable)
  ap_reset_regs: assert property (disable iff (1'b0)
    reset |-> (counter == '0 && counter_msb_d1 == 1'b0));
  ap_reset_outs: assert property (disable iff (1'b0)
    reset |-> (seg == 7'b1111111 && dp == 1'b1 && an == 4'b1111 && digit == 2'b00));

  // Counter behavior and edge generation
  ap_counter_inc:  assert property (!$past(reset) |-> counter == $past(counter) + 1'b1);
  ap_msb_delay:    assert property (!$past(reset) |-> counter_msb_d1 == $past(counter[COUNTER_WIDTH-1]));
  ap_edge_def:     assert property (counter_edge == (~counter_msb_d1 & counter[COUNTER_WIDTH-1]));

  // Digit timing: increment only on edge, hold otherwise
  ap_digit_on_edge: assert property (counter_edge |-> digit == $past(digit) + 2'd1);
  ap_digit_hold:    assert property (!counter_edge |-> $stable(digit));

  // an/seg update protocol
  ap_update_mux0: assert property (counter_edge && $past(digit)==2'b00 |-> (an==4'b1110 && seg==seg0));
  ap_update_mux1: assert property (counter_edge && $past(digit)==2'b01 |-> (an==4'b1101 && seg==seg1));
  ap_update_mux2: assert property (counter_edge && $past(digit)==2'b10 |-> (an==4'b1011 && seg==seg2));
  ap_update_mux3: assert property (counter_edge && $past(digit)==2'b11 |-> (an==4'b0111 && seg==seg3));
  ap_hold_no_edge: assert property (!counter_edge |-> ($stable(an) && $stable(seg)));

  // Active-low an: exactly one digit enabled once scanning starts; dp stays high
  ap_an_onehot: assert property ((an != 4'b1111) |-> $onehot(~an));
  ap_dp_const:  assert property (dp == 1'b1);

  // End-to-end decode: selected an must match corresponding value nibble
  ap_sel0: assert property ((an==4'b1110) |-> (seg == hex2seg(value[3:0])));
  ap_sel1: assert property ((an==4'b1101) |-> (seg == hex2seg(value[7:4])));
  ap_sel2: assert property ((an==4'b1011) |-> (seg == hex2seg(value[11:8])));
  ap_sel3: assert property ((an==4'b0111) |-> (seg == hex2seg(value[15:12])));

  // Also verify each val2seg instance output matches truth table (regardless of selection)
  ap_v2s0: assert property (seg0 == hex2seg(value[3:0]));
  ap_v2s1: assert property (seg1 == hex2seg(value[7:4]));
  ap_v2s2: assert property (seg2 == hex2seg(value[11:8]));
  ap_v2s3: assert property (seg3 == hex2seg(value[15:12]));

  // No-X in key controls during normal operation
  ap_no_x: assert property (!$isunknown({an, seg, dp, digit, counter_edge, counter_msb_d1}));

  // Coverage: observe a full scan cycle and edges
  cv_edge:        cover property (counter_edge);
  cv_full_cycle:  cover property (
    (counter_edge && $past(digit)==2'b00) ##1
    (counter_edge && $past(digit)==2'b01) ##1
    (counter_edge && $past(digit)==2'b10) ##1
    (counter_edge && $past(digit)==2'b11)
  );
  cv_an_sequence: cover property (
    (counter_edge && an==4'b1110) ##1
    (counter_edge && an==4'b1101) ##1
    (counter_edge && an==4'b1011) ##1
    (counter_edge && an==4'b0111)
  );

endmodule

// Bind into DUT (access internal nets)
bind seg7 seg7_assert #(.COUNTER_WIDTH(COUNTER_WIDTH)) seg7_assert_i
(
  .clk(clk),
  .reset(reset),
  .counter(counter),
  .counter_msb_d1(counter_msb_d1),
  .counter_edge(counter_edge),
  .digit(digit),
  .value(value),
  .seg(seg),
  .dp(dp),
  .an(an),
  .seg0(seg0),
  .seg1(seg1),
  .seg2(seg2),
  .seg3(seg3)
);