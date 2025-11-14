// SVA for seven_segment_display
// Focus: correctness of hex decoding, muxing/rotation, timing/stability, and simple coverage.

module seven_segment_display_sva
(
  input  logic        clk,
  input  logic [15:0] num_in,
  input  logic [6:0]  dig,
  input  logic        dp,
  input  logic        neg,
  input  logic        clr,
  input  logic [3:0]  dig_sel,

  // internal DUT regs (bound hierarchically)
  input  logic [6:0]  dig1,
  input  logic [6:0]  dig2,
  input  logic [6:0]  dig3,
  input  logic [6:0]  dig4,
  input  logic [19:0] clk_div
);

  function automatic logic [6:0] hex2seg (input logic [3:0] h);
    case (h)
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
    endcase
  endfunction

  default clocking cb @ (posedge clk); endclocking

  logic started;
  initial started = 1'b0;
  always @(posedge clk) started <= 1'b1;

  // Static outputs
  assert property (started |-> dp==1'b0 && neg==1'b0 && clr==1'b0);

  // Decoder correctness for each internal digit
  assert property (started |-> dig1 == hex2seg(num_in[3:0]));
  assert property (started |-> dig2 == hex2seg(num_in[7:4]));
  assert property (started |-> dig3 == hex2seg(num_in[11:8]));
  assert property (started |-> dig4 == hex2seg(num_in[15:12]));

  // Counter increments modulo 2^20
  assert property (started |-> clk_div == $past(clk_div) + 20'd1);

  // dig_sel one-hot or zero
  assert property (started |-> (dig_sel==4'b0000) || $onehot(dig_sel));

  // dig_sel, dig change only on rollover; hold otherwise
  assert property (started && (clk_div != 20'd0) |-> $stable(dig_sel) && $stable(dig));
  assert property (started && $changed(dig_sel) |-> $past(clk_div==20'd0));
  assert property (started && $changed(dig)     |-> $past(clk_div==20'd0));

  // Rotation behavior at rollover
  assert property (started && (clk_div==20'd0) && (dig_sel==4'b0000) |=> dig_sel==4'b0001);
  assert property (started && (clk_div==20'd0) && (dig_sel!=4'b0000)
                   |=> dig_sel == { $past(dig_sel)[0], $past(dig_sel)[3:1] });

  // Mux selection at rollover (uses sampled "old" dig_sel)
  assert property (started && (clk_div==20'd0) && (dig_sel!=4'b0000)
                   |-> ((dig_sel==4'b0001 && dig==dig1) ||
                        (dig_sel==4'b0010 && dig==dig4) ||
                        (dig_sel==4'b0100 && dig==dig3) ||
                        (dig_sel==4'b1000 && dig==dig2)));
  // No update when dig_sel==0 at rollover
  assert property (started && (clk_div==20'd0) && (dig_sel==4'b0000) |-> $stable(dig));

  // End-to-end: displayed segments match prior-cycle selected nibble
  assert property (started && (clk_div==20'd0) && (dig_sel==4'b0001) |-> dig == $past(hex2seg(num_in[3:0])));
  assert property (started && (clk_div==20'd0) && (dig_sel==4'b0010) |-> dig == $past(hex2seg(num_in[15:12])));
  assert property (started && (clk_div==20'd0) && (dig_sel==4'b0100) |-> dig == $past(hex2seg(num_in[11:8])));
  assert property (started && (clk_div==20'd0) && (dig_sel==4'b1000) |-> dig == $past(hex2seg(num_in[7:4])));

  // Coverage: observe full rotation across rollover events
  sequence e; clk_div==20'd0; endsequence
  cover property (started and
                  (e && dig_sel==4'b0001) ##[1:$]
                  (e && dig_sel==4'b1000) ##[1:$]
                  (e && dig_sel==4'b0100) ##[1:$]
                  (e && dig_sel==4'b0010) ##[1:$]
                  (e && dig_sel==4'b0001));

  // Coverage: see all 16 hex patterns on the driven display
  genvar i;
  generate
    for (i=0; i<16; i++) begin : C_DIG_ALL_HEX
      cover property (started && (clk_div==20'd0) && (dig == hex2seg(i[3:0])));
    end
  endgenerate

endmodule

bind seven_segment_display seven_segment_display_sva sva
(
  .clk(clk),
  .num_in(num_in),
  .dig(dig),
  .dp(dp),
  .neg(neg),
  .clr(clr),
  .dig_sel(dig_sel),
  .dig1(dig1),
  .dig2(dig2),
  .dig3(dig3),
  .dig4(dig4),
  .clk_div(clk_div)
);