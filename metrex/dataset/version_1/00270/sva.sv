// SVA for binary_gray_updown and binary_to_gray_converter

// Assertions for the top module
module sva_binary_gray_updown (
    input clk,
    input rst,
    input en,
    input up,
    input select,
    input [2:0] BIN,
    input [2:0] GRAY,
    input [3:0] count
);

  function automatic [2:0] bin2gray3(input [2:0] b);
    return {b[2], b[2]^b[1], b[1]^b[0]};
  endfunction

  // Reset check (no disable iff)
  a_reset_count_zero: assert property (@(posedge clk)
    rst |-> (count == 4'd0) && $stable(GRAY)
  );

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  // Hold when disabled
  a_hold_when_disabled: assert property (!en |-> $stable({count, GRAY}));

  // Conversion mode: GRAY matches function, count holds
  a_conv_gray_matches: assert property (en && select |-> (GRAY == bin2gray3(BIN)) && $stable(count));

  // Counter mode: increment/decrement and GRAY forced to 0
  a_cnt_inc: assert property (en && !select && up  |-> (count == $past(count) + 4'd1) && (GRAY == 3'b000));
  a_cnt_dec: assert property (en && !select && !up |-> (count == $past(count) - 4'd1) && (GRAY == 3'b000));

  // No X on GRAY in conversion mode when BIN is known
  a_no_x_gray_in_conv: assert property (en && select && !$isunknown(BIN) |-> !$isunknown(GRAY));

  // Gray property: one-bit change when BIN changes by +/-1 across consecutive conversion cycles
  a_gray_onebit_inc: assert property ($past(en && select) && en && select && (BIN == $past(BIN) + 3'd1)
                                     |-> $onehot(GRAY ^ $past(GRAY)));
  a_gray_onebit_dec: assert property ($past(en && select) && en && select && (BIN == $past(BIN) - 3'd1)
                                     |-> $onehot(GRAY ^ $past(GRAY)));

  // Coverage
  c_reset:         cover property (rst ##1 !rst);
  c_mode_conv:     cover property (en && select);
  c_mode_cnt:      cover property (en && !select);
  c_inc:           cover property (en && !select && up);
  c_dec:           cover property (en && !select && !up);
  c_wrap_inc:      cover property (en && !select && up && count == 4'hF ##1 count == 4'h0);
  c_wrap_dec:      cover property (en && !select && !up && count == 4'h0 ##1 count == 4'hF);
  c_mode_switch_c2k: cover property (en && select ##1 en && !select);
  c_mode_switch_k2c: cover property (en && !select ##1 en && select);
  c_bin0: cover property (en && select && BIN == 3'h0);
  c_bin1: cover property (en && select && BIN == 3'h1);
  c_bin2: cover property (en && select && BIN == 3'h2);
  c_bin3: cover property (en && select && BIN == 3'h3);
  c_bin4: cover property (en && select && BIN == 3'h4);
  c_bin5: cover property (en && select && BIN == 3'h5);
  c_bin6: cover property (en && select && BIN == 3'h6);
  c_bin7: cover property (en && select && BIN == 3'h7);

endmodule

// Assertions for the converter
module sva_binary_to_gray_converter (
    input [2:0] bin,
    input [2:0] gray
);
  a_b2g_func: assert property (@(*) gray === {bin[2], bin[2]^bin[1], bin[1]^bin[0]});
  a_no_x_when_bin_known: assert property (@(*) !$isunknown(bin) |-> !$isunknown(gray));
endmodule

// Bind SVA to DUTs
bind binary_gray_updown          sva_binary_gray_updown          SVA_binary_gray_updown          (.*);
bind binary_to_gray_converter    sva_binary_to_gray_converter    SVA_binary_to_gray_converter    (.*);