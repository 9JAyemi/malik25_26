// SVA checker for CRC_16 (concise, focuses on key behavior)
// Note: a_update matches this RTL’s blocking-semantics effect.
module CRC_16_sva;
  // Bound into CRC_16 scope; direct access to DUT signals (BITVAL, Enable, CLK, RST, CRC, inv)
  default clocking cb @ (posedge CLK); endclocking

  // Past-valid flag
  logic past_v;
  always @(posedge CLK or posedge RST) begin
    if (RST) past_v <= 1'b0;
    else     past_v <= 1'b1;
  end

  // Effective feedback used by this RTL (due to blocking and inv depending on CRC[15] after first assignment)
  logic inv_eff_q;
  always @(posedge CLK) inv_eff_q <= BITVAL ^ CRC[14];

  // Basic combinational and reset checks
  a_inv:       assert property (inv == (BITVAL ^ CRC[15]));
  a_rst_async: assert property (@(posedge RST) CRC == 16'h0);
  a_rst_sync:  assert property (RST |-> (CRC == 16'h0));

  // Hold when not enabled
  a_hold: assert property (disable iff (!past_v || RST)
                           $past(!RST) && $past(!Enable) |-> CRC == $past(CRC));

  // Next-state transform when enabled (matches this RTL)
  a_update: assert property (disable iff (!past_v || RST)
                             $past(!RST) && $past(Enable) |->
                               (CRC[15:13] == $past(CRC[14:12])) &&
                               (CRC[12]    == ($past(CRC[11]) ^ inv_eff_q)) &&
                               (CRC[11:6]  == $past(CRC[10:5])) &&
                               (CRC[5]     == ($past(CRC[4])  ^ inv_eff_q)) &&
                               (CRC[4:1]   == $past(CRC[3:0])) &&
                               (CRC[0]     == inv_eff_q));

  // No X on CRC out of reset
  a_no_x: assert property (!RST |-> !$isunknown(CRC));

  // Coverage
  c_reset:  cover property (RST ##1 !RST);
  c_hold:   cover property (disable iff (!past_v || RST) $past(!Enable) && !RST);
  c_en_b0:  cover property (disable iff (!past_v || RST) $past(Enable) && ($past(BITVAL)==1'b0) && !RST);
  c_en_b1:  cover property (disable iff (!past_v || RST) $past(Enable) && ($past(BITVAL)==1'b1) && !RST);
  c_inj0:   cover property (disable iff (!past_v || RST) $past(Enable) && !inv_eff_q);
  c_inj1:   cover property (disable iff (!past_v || RST) $past(Enable) &&  inv_eff_q);
endmodule

bind CRC_16 CRC_16_sva u_crc16_sva();