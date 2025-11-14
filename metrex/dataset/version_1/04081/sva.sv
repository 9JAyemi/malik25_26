// SVA for cf_ss_422to444
// Concise, high-signal-quality checks and key functional cover

bind cf_ss_422to444 cf_ss_422to444_sva();

module cf_ss_422to444_sva;

  // Use DUT scope directly via bind-without-ports
  // default clock and a past-valid guard
  bit past_valid;
  always_ff @(posedge clk) past_valid <= 1'b1;

  default clocking cb @(posedge clk); endclocking
  default disable iff (!past_valid);

  // Small helper for the [1 2 1] / 4 filter
  function automatic [7:0] filt3x8(input [7:0] x0, input [7:0] x1, input [7:0] x2);
    filt3x8 = (x0 + x2 + (x1 << 1)) >> 2;
  endfunction

  // 1) Handshake/control pipeline integrity (1->2->3 cycle delay)
  assert property (s422_vs_d   == $past(s422_vs));
  assert property (s422_vs_2d  == $past(s422_vs_d));
  assert property (s422_vs_3d  == $past(s422_vs_2d));

  assert property (s422_hs_d   == $past(s422_hs));
  assert property (s422_hs_2d  == $past(s422_hs_d));
  assert property (s422_hs_3d  == $past(s422_hs_2d));

  assert property (s422_de_d   == $past(s422_de));
  assert property (s422_de_2d  == $past(s422_de_d));
  assert property (s422_de_3d  == $past(s422_de_2d));

  // 2) Cr/Cb selector behavior
  // toggle on active de, else force to init
  assert property ( s422_de  |=> Cr_Cb_sel == ~$past(Cr_Cb_sel) );
  assert property (!s422_de  |=> Cr_Cb_sel ==  Cr_Cb_sel_init );

  // 3) 4:2:2 byte packing into 24b shift register (uses old Cr_Cb_sel value)
  // When enabled, update according to previous selector; else hold
  assert property (!s422_de |=> s422_data_d == $past(s422_data_d));

  assert property ( s422_de && ($past(Cr_Cb_sel)==1'b1)
                    |=> s422_data_d == { $past(s422_data[15:8]), $past(s422_data[7:0]), $past(s422_data_d[7:0]) } );

  assert property ( s422_de && ($past(Cr_Cb_sel)==1'b0)
                    |=> s422_data_d == { $past(s422_data_d[23:16]), $past(s422_data[7:0]), $past(s422_data[15:8]) } );

  // 4) Data staging enables and holds
  assert property ( s422_de_d    |=> s422_data_2d == $past(s422_data_d) );
  assert property (!s422_de_d    |=> s422_data_2d == $past(s422_data_2d) );

  assert property ( s422_de_2d   |=> s422_data_3d == $past(s422_data_2d) );
  assert property (!s422_de_2d   |=> s422_data_3d == $past(s422_data_3d) );

  // 5) Filtered chroma reconstruction
  // R and B are registered from previous-cycle weighted sum
  assert property ( R == $past( filt3x8(s422_data_d[23:16], s422_data_2d[23:16], s422_data_3d[23:16]) ) );
  assert property ( B == $past( filt3x8(s422_data_d[7:0],   s422_data_2d[7:0],   s422_data_3d[7:0])   ) );

  // 6) Output timing: 3-cycle latency for syncs/DE
  assert property ( s444_vs == $past(s422_vs,3) );
  assert property ( s444_hs == $past(s422_hs,3) );
  assert property ( s444_de == $past(s422_de,3) );

  // 7) Output data correctness and gating
  // When not active, zero; when active, use prior-cycle R/Y/B (due to NBA semantics)
  assert property ( !s422_de_3d |=> s444_data == 24'd0 );
  assert property (  s422_de_3d |=> s444_data == { $past(R), $past(s422_data_3d[15:8]), $past(B) } );

  // 8) X-propagation guard on outputs
  assert property ( !$isunknown({s444_vs, s444_hs, s444_de, s444_data}) );

  // 9) Functional coverage (key modes exercised)
  cover property ( s422_de && ($past(Cr_Cb_sel)==1'b0) );
  cover property ( s422_de && ($past(Cr_Cb_sel)==1'b1) );

  cover property ( s422_de [*4] );                          // run of active pixels
  cover property ( s444_de && (s444_data != 24'd0) );       // nonzero active output
  cover property ( $changed(R) && $changed(B) );            // filter dynamics seen

endmodule