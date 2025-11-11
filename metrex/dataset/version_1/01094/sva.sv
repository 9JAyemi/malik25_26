// SVA for top_module and sub-block functionality
// Focused, concise checks + essential coverage

// Bind into DUT
bind top_module top_module_sva top_sva_inst (
  .CLK     (CLK),
  .RESET   (RESET),
  .UP_DOWN (UP_DOWN),
  .gray    (gray),
  .OUT     (OUT),
  .binary  (binary),
  .counter (counter),
  .sum     (sum)
);

module top_module_sva (
  input logic        CLK,
  input logic        RESET,
  input logic        UP_DOWN,
  input logic [3:0]  gray,
  input logic [3:0]  OUT,
  input logic [3:0]  binary,
  input logic [3:0]  counter,
  input logic [3:0]  sum
);

  // helper
  function automatic logic [3:0] g2b4 (input logic [3:0] g);
    g2b4[3]=g[3];
    g2b4[2]=g2b4[3]^g[2];
    g2b4[1]=g2b4[2]^g[1];
    g2b4[0]=g2b4[1]^g[0];
  endfunction

  // basic sanity: inputs known, outputs known post-reset release
  ap_inputs_known: assert property (@(posedge CLK) !$isunknown(RESET) && !$isunknown(UP_DOWN));
  ap_outs_known:   assert property (@(posedge CLK)
                        disable iff (RESET || $past(RESET,1,1'b1))
                        !$isunknown(OUT) && !$isunknown(counter));

  // synchronous reset behavior
  ap_reset_nextzero: assert property (@(posedge CLK) RESET |=> (OUT==4'h0 && counter==4'h0));
  ap_reset_hold_zero: assert property (@(posedge CLK)
                           (RESET && $past(RESET,1,1'b0)) |-> (OUT==4'h0 && counter==4'h0));

  // top OUT counting behavior (mod-16 implicit)
  ap_count_up_top:   assert property (@(posedge CLK) disable iff (RESET)
                         UP_DOWN  |=> OUT == $past(OUT)     + 4'd1);
  ap_count_dn_top:   assert property (@(posedge CLK) disable iff (RESET)
                        !UP_DOWN  |=> OUT == $past(OUT)     - 4'd1);

  // sub counter behavior
  ap_count_up_ctr:   assert property (@(posedge CLK) disable iff (RESET)
                         UP_DOWN  |=> counter == $past(counter) + 4'd1);
  ap_count_dn_ctr:   assert property (@(posedge CLK) disable iff (RESET)
                        !UP_DOWN  |=> counter == $past(counter) - 4'd1);

  // top OUT must track sub-counter 1:1 (same RTL)
  ap_equiv_outs:     assert property (@(posedge CLK) disable iff (RESET) OUT == counter);

  // gray->binary correct
  ap_gray2bin:       assert property (@(posedge CLK) binary == g2b4(gray));

  // functional sum correct (4-bit wrap)
  ap_sum:            assert property (@(posedge CLK) sum == (binary + counter));

  // Coverage: exercise both directions and wrap-around
  cp_up_dir:         cover property (@(posedge CLK) disable iff (RESET) UP_DOWN);
  cp_dn_dir:         cover property (@(posedge CLK) disable iff (RESET) !UP_DOWN);
  cp_wrap_up:        cover property (@(posedge CLK) disable iff (RESET)
                          $past(OUT)==4'hF && UP_DOWN |=> OUT==4'h0);
  cp_wrap_dn:        cover property (@(posedge CLK) disable iff (RESET)
                          $past(OUT)==4'h0 && !UP_DOWN |=> OUT==4'hF);
  // Gray input bits toggle at least once
  genvar i;
  generate
    for (i=0;i<4;i++) begin : gbit_cov
      cp_gray_bit_toggle: cover property (@(posedge CLK) $changed(gray[i]));
    end
  endgenerate
  // Sum overflow (carry) observed
  cp_sum_carry: cover property (@(posedge CLK) disable iff (RESET)
                      ({1'b0,$past(binary)} + {1'b0,$past(counter)})[4]);

endmodule