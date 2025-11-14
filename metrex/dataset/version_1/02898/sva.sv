// SVA for gray_code_counter
// Bind this checker to the DUT to verify reset, incrementing, and Gray-code correctness.

module gray_code_counter_sva (
  input  logic        CLK,
  input  logic        RST,
  input  logic [7:0]  count_gray,
  input  logic [7:0]  count_binary
);

  function automatic [7:0] bin2gray (input [7:0] b);
    return b ^ (b >> 1);
  endfunction

  // During reset, registers are held at zero (checked at clock edge)
  a_reset_zero: assert property (@(posedge CLK) !RST |-> (count_binary==8'h00 && count_gray==8'h00));

  // No X/Z when out of reset
  a_no_x: assert property (@(posedge CLK) disable iff (!RST)
                           !$isunknown({count_binary, count_gray}));

  // Binary counter increments by 1 mod 256 on each enabled cycle
  a_bin_incr: assert property (@(posedge CLK) disable iff (!RST)
                               $past(RST) |-> ((count_binary - $past(count_binary)) == 8'd1));

  // Gray code equals bin2gray(previous binary value) (one-cycle pipeline)
  a_gray_map_prev_bin: assert property (@(posedge CLK) disable iff (!RST)
                                        $past(RST) |-> (count_gray == bin2gray($past(count_binary))));

  // Successive Gray outputs differ by exactly one bit (after first post-reset cycle)
  a_gray_onebit: assert property (@(posedge CLK) disable iff (!RST)
                                  $past(RST) |-> $onehot(count_gray ^ $past(count_gray)));

  // Coverage: wrap-around observed and still one-bit Gray transition
  c_wrap: cover property (@(posedge CLK) disable iff (!RST)
                          ($past(count_binary)==8'hFF) && (count_binary==8'h00) &&
                          $onehot(count_gray ^ $past(count_gray)));

  // Coverage: every Gray bit toggles at least once
  genvar i;
  generate
    for (i=0;i<8;i++) begin : C_BIT_TOGGLE
      cover property (@(posedge CLK) disable iff (!RST) $changed(count_gray[i]));
    end
  endgenerate

endmodule

// Bind into the DUT type so internal count_binary is visible for connection
bind gray_code_counter gray_code_counter_sva sva (
  .CLK(CLK),
  .RST(RST),
  .count_gray(count_gray),
  .count_binary(count_binary)
);