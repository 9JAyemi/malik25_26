// Bindable SVA for spi
module spi_sva;
  // This module is intended to be bound into spi; it relies on spi internals.
  default clocking cb @(posedge clock); endclocking

  bit init;
  always_ff @(posedge clock) init <= 1'b1;
  default disable iff (!init);

  // Combinational ties
  assert property (sck == counter[0]);
  assert property (enable_n == counter[4]);
  assert property (sdo == shiftout[7]);
  assert property (ena_shout_load == ((start | sck) & g_ena));

  // g_ena control
  assert property (!halfspeed |=> g_ena == 1'b1);
  assert property (halfspeed && start |=> g_ena == 1'b0);
  assert property (halfspeed && !start && enable_n |=> g_ena == 1'b1);
  assert property (halfspeed && !start && !enable_n |=> g_ena == ~$past(g_ena));

  // Counter behavior
  assert property (g_ena && start |=> counter == 5'd0);
  assert property (g_ena && !start && !enable_n |=> counter == $past(counter) + 5'd1);
  assert property ((!g_ena) || (g_ena && !start && enable_n) |=> counter == $past(counter));

  // bsync pulseing
  assert property (g_ena && start |=> bsync == 1'b1);
  assert property (g_ena && !start && sck |=> bsync == 1'b0);

  // shift-in sampling on sck==0
  assert property (g_ena && !start && !sck |=> shiftin == { $past(shiftin[5:0]), $past(sdi) });
  assert property (!(g_ena && !start && !sck) |=> shiftin == $past(shiftin));

  // dout captures after 8 samples (at counter[3:1]==3'b111 while enable_n==0 and sck==0)
  assert property (g_ena && !start && !sck && (&counter[3:1]) && !enable_n
                   |=> dout == { $past(shiftin[6:0]), $past(sdi) });
  assert property (!(g_ena && !start && !sck && (&counter[3:1]) && !enable_n)
                   |=> dout == $past(dout));

  // shift-out load/rotate when (start|sck) & g_ena
  assert property (ena_shout_load && start |=> shiftout == $past(din));
  assert property (ena_shout_load && !start |=> shiftout == { $past(shiftout[6:0]), $past(shiftout[0]) });
  assert property (!ena_shout_load |=> shiftout == $past(shiftout));

  // Once enable_n goes high (no new start), hold counter stable
  assert property (enable_n && !start |=> $stable(counter));

  // Coverage
  sequence dout_update_s;
    g_ena && !start && !sck && (&counter[3:1]) && !enable_n;
  endsequence

  cover property (g_ena && !halfspeed && start ##[1:32] dout_update_s);
  cover property (g_ena && halfspeed && start ##[1:64] dout_update_s);
  cover property (g_ena && start ##1 (!sck && g_ena && !start)[*8] ##1 dout_update_s);
  cover property (ena_shout_load && start ##1 (ena_shout_load && !start)[*8]);
endmodule

bind spi spi_sva sva_spi_i();