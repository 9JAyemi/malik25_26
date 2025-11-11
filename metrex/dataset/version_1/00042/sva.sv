// SVA for BIN_DEC2
// Bind this module to the DUT to check correctness and provide coverage.

module BIN_DEC2_sva (input logic [15:0] B2,
                     input logic [19:0] bcdout2);

  // Reference model: 16-bit unsigned binary to 5-digit BCD
  function automatic logic [19:0] bcd_ref(input logic [15:0] bin);
    int unsigned v, d0, d1, d2, d3, d4;
    begin
      v = bin;
      d0 = v % 10; v = v / 10;
      d1 = v % 10; v = v / 10;
      d2 = v % 10; v = v / 10;
      d3 = v % 10; v = v / 10;
      d4 = v % 10;
      return {logic'(d4[3:0]), logic'(d3[3:0]), logic'(d2[3:0]), logic'(d1[3:0]), logic'(d0[3:0])};
    end
  endfunction

  // Helper: BCD to unsigned for monotonic check
  function automatic int unsigned bcd_to_uint(input logic [19:0] b);
    return (b[19:16]*10000) + (b[15:12]*1000) + (b[11:8]*100) + (b[7:4]*10) + b[3:0];
  endfunction

  // Generate a clean sampling event on input change; check in next delta (##0) for settled comb result
  event ev_in;
  always @(B2) -> ev_in;

  // 1) Golden functional equivalence
  ap_func_eq: assert property (@(ev_in) 1 |-> ##0 (bcdout2 == bcd_ref(B2)))
    else $error("BIN_DEC2: functional mismatch: B2=%0d bcdout2=%05h exp=%05h", B2, bcdout2, bcd_ref(B2));

  // 2) Output nibbles are valid BCD (0..9), and MS digit is bounded (<=6 for max 65535)
  ap_bcd_digits_valid: assert property (@(ev_in) 1 |-> ##0
    ((bcdout2[3:0]  <= 9) &&
     (bcdout2[7:4]  <= 9) &&
     (bcdout2[11:8] <= 9) &&
     (bcdout2[15:12]<= 9) &&
     (bcdout2[19:16]<= 6)))
    else $error("BIN_DEC2: non-BCD digit detected: %05h", bcdout2);

  // 3) No X/Z on outputs when inputs are known
  ap_no_x: assert property (@(ev_in) !$isunknown(B2) |-> ##0 !$isunknown(bcdout2))
    else $error("BIN_DEC2: X/Z on output for known input");

  // 4) Local monotonicity: if input increments by 1, decoded BCD increments by 1
  ap_plus1: assert property (@(ev_in)
    (!$isunknown($past(B2,1,ev_in)) && !$isunknown(B2) && ($past(B2,1,ev_in)+1 == B2))
      |-> ##0 (bcd_to_uint(bcdout2) == bcd_to_uint($past(bcdout2,1,ev_in)) + 1))
    else $error("BIN_DEC2: +1 monotonicity failed");

  // 5) Structural range sharpening: suppress leading digits when below thresholds
  ap_leading_zero_4: assert property (@(ev_in) (B2 <= 16'd9999)  |-> ##0 (bcdout2[19:16] == 0));
  ap_leading_zero_3: assert property (@(ev_in) (B2 <= 16'd999)   |-> ##0 (bcdout2[19:16] == 0 && bcdout2[15:12] == 0));
  ap_leading_zero_2: assert property (@(ev_in) (B2 <= 16'd99)    |-> ##0 (bcdout2[19:16] == 0 && bcdout2[15:12] == 0 && bcdout2[11:8] == 0));
  ap_leading_zero_1: assert property (@(ev_in) (B2 <= 16'd9)     |-> ##0 (bcdout2[19:16] == 0 && bcdout2[15:12] == 0 && bcdout2[11:8] == 0 && bcdout2[7:4]==0));

  // Coverage: key edges and representative points
  cp_0:      cover property (@(ev_in) ##0 (B2 == 16'd0      && bcdout2 == bcd_ref(16'd0)));
  cp_9:      cover property (@(ev_in) ##0 (B2 == 16'd9      && bcdout2 == bcd_ref(16'd9)));
  cp_10:     cover property (@(ev_in) ##0 (B2 == 16'd10     && bcdout2 == bcd_ref(16'd10)));
  cp_99:     cover property (@(ev_in) ##0 (B2 == 16'd99     && bcdout2 == bcd_ref(16'd99)));
  cp_100:    cover property (@(ev_in) ##0 (B2 == 16'd100    && bcdout2 == bcd_ref(16'd100)));
  cp_999:    cover property (@(ev_in) ##0 (B2 == 16'd999    && bcdout2 == bcd_ref(16'd999)));
  cp_1000:   cover property (@(ev_in) ##0 (B2 == 16'd1000   && bcdout2 == bcd_ref(16'd1000)));
  cp_9999:   cover property (@(ev_in) ##0 (B2 == 16'd9999   && bcdout2 == bcd_ref(16'd9999)));
  cp_10000:  cover property (@(ev_in) ##0 (B2 == 16'd10000  && bcdout2 == bcd_ref(16'd10000)));
  cp_max:    cover property (@(ev_in) ##0 (B2 == 16'd65535  && bcdout2 == bcd_ref(16'd65535)));
  cp_rand:   cover property (@(ev_in) ##0 (B2 == 16'd12345  && bcdout2 == bcd_ref(16'd12345)));

endmodule

// Bind into the DUT
bind BIN_DEC2 BIN_DEC2_sva u_BIN_DEC2_sva (.B2(B2), .bcdout2(bcdout2));