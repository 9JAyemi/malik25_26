// SVA for sp_mux_9to1_sel4_6_1
bind sp_mux_9to1_sel4_6_1 sp_mux_9to1_sel4_6_1_sva();

module sp_mux_9to1_sel4_6_1_sva;

  // Fire assertions/coverage whenever any relevant signal changes
  event ev_in;
  always @({din1,din2,din3,din4,din5,din6,din7,din8,din9,din10,dout}) -> ev_in;

  // Functional correctness: dout equals the mux function of sel and inputs
  assert property (@(ev_in)
    dout == ( sel[3] ? din9
           : (sel[2] ? (sel[1] ? (sel[0]? din8 : din7)
                               : (sel[0]? din6 : din5))
                     : (sel[1] ? (sel[0]? din4 : din3)
                               : (sel[0]? din2 : din1)) ) )
  ) else $error("Mux function mismatch");

  // sel[3] dominance: when sel[3]==1, dout must be din9 regardless of lower bits
  assert property (@(ev_in) sel[3] |-> dout == din9)
    else $error("sel[3] dominance violated");

  // No-X propagation: when all controls/data known, dout must be known
  assert property (@(ev_in)
    !$isunknown({din1,din2,din3,din4,din5,din6,din7,din8,din9,sel}) |-> !$isunknown(dout)
  ) else $error("Unknowns propagated to dout");

  // Observability: when the currently selected input changes, dout must change
  assert property (@(ev_in) (!sel[3] && sel[2:0]==3'd0 && $changed(din1)) |-> $changed(dout));
  assert property (@(ev_in) (!sel[3] && sel[2:0]==3'd1 && $changed(din2)) |-> $changed(dout));
  assert property (@(ev_in) (!sel[3] && sel[2:0]==3'd2 && $changed(din3)) |-> $changed(dout));
  assert property (@(ev_in) (!sel[3] && sel[2:0]==3'd3 && $changed(din4)) |-> $changed(dout));
  assert property (@(ev_in) (!sel[3] && sel[2:0]==3'd4 && $changed(din5)) |-> $changed(dout));
  assert property (@(ev_in) (!sel[3] && sel[2:0]==3'd5 && $changed(din6)) |-> $changed(dout));
  assert property (@(ev_in) (!sel[3] && sel[2:0]==3'd6 && $changed(din7)) |-> $changed(dout));
  assert property (@(ev_in) (!sel[3] && sel[2:0]==3'd7 && $changed(din8)) |-> $changed(dout));
  assert property (@(ev_in) ( sel[3]                        && $changed(din9)) |-> $changed(dout));

  // When sel[3]==1 and din9 is stable, changes on lower sel bits must not affect dout
  assert property (@(ev_in) sel[3] && $changed(sel[2:0]) && $stable(din9) |-> $stable(dout));

  // Stability: if all inputs and select are stable, dout must be stable
  assert property (@(ev_in) $stable({din1,din2,din3,din4,din5,din6,din7,din8,din9,sel}) |-> $stable(dout));

  // Coverage: hit all 16 select codes
  genvar i;
  generate
    for (i=0; i<16; i++) begin : gen_sel_cvr
      localparam logic [3:0] SV = i[3:0];
      cover property (@(ev_in) sel == SV);
    end
  endgenerate

  // Coverage: edges on each select bit
  cover property (@(ev_in) $rose(sel[0]));  cover property (@(ev_in) $fell(sel[0]));
  cover property (@(ev_in) $rose(sel[1]));  cover property (@(ev_in) $fell(sel[1]));
  cover property (@(ev_in) $rose(sel[2]));  cover property (@(ev_in) $fell(sel[2]));
  cover property (@(ev_in) $rose(sel[3]));  cover property (@(ev_in) $fell(sel[3]));

  // Coverage: each data path observed toggling while selected
  cover property (@(ev_in) !sel[3] && sel[2:0]==3'd0 && $changed(din1));
  cover property (@(ev_in) !sel[3] && sel[2:0]==3'd1 && $changed(din2));
  cover property (@(ev_in) !sel[3] && sel[2:0]==3'd2 && $changed(din3));
  cover property (@(ev_in) !sel[3] && sel[2:0]==3'd3 && $changed(din4));
  cover property (@(ev_in) !sel[3] && sel[2:0]==3'd4 && $changed(din5));
  cover property (@(ev_in) !sel[3] && sel[2:0]==3'd5 && $changed(din6));
  cover property (@(ev_in) !sel[3] && sel[2:0]==3'd6 && $changed(din7));
  cover property (@(ev_in) !sel[3] && sel[2:0]==3'd7 && $changed(din8));
  cover property (@(ev_in)  sel[3]                      && $changed(din9));

endmodule