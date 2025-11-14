// SVA for iq_comp. Bind with: bind iq_comp iq_comp_sva u_iq_comp_sva(.*);

module iq_comp_sva (
  input clk, RESETn,
  input freeze_iqcomp,
  input [1:0] op_mode,
  input [3:0] Ix, Qx,
  input  signed [12:0] Wr_in, Wj_in,
  input  signed [3:0]  Iy, Qy,
  input               settled,
  input  signed [12:0] Wr, Wj
);
  localparam BYPASS = 2'b00;
  localparam INT_W  = 2'b01;
  localparam EXT_W  = 2'b10;
  localparam CONT_W = 2'b11;
  localparam int M  = 9;

  function automatic signed [3:0] sat4(input signed [4:0] x);
    if (x < -4'sd8)      sat4 = -4'sd8;
    else if (x > 4'sd7)  sat4 =  4'sd7;
    else                 sat4 =  x[3:0];
  endfunction

  function automatic signed [3:0] ix_s_fn(input [3:0] x);
    ix_s_fn = $signed(x - 4'd8);
  endfunction
  function automatic signed [3:0] qx_s_fn(input [3:0] x);
    qx_s_fn = $signed(x - 4'd8);
  endfunction

  function automatic signed [3:0] calc_iy(
    input [1:0] mode, input [3:0] ix, input [3:0] qx,
    input signed [12:0] wr, input signed [12:0] wj,
    input signed [12:0] wr_in_f, input signed [12:0] wj_in_f
  );
    automatic signed [3:0] ix_s = ix_s_fn(ix);
    automatic signed [3:0] qx_s = qx_s_fn(qx);
    automatic signed [12:0] wur = (mode==INT_W) ? wr     : wr_in_f;
    automatic signed [12:0] wuj = (mode==INT_W) ? wj     : wj_in_f;
    automatic signed [25:0] i1  = ($signed(ix_s) <<< M) + $signed((wur*ix_s) + (wuj*qx_s));
    automatic signed [4:0]  i2  = $signed(i1) >>> M;
    calc_iy = (mode==BYPASS || mode==CONT_W) ? ix_s : sat4(i2);
  endfunction

  function automatic signed [3:0] calc_qy(
    input [1:0] mode, input [3:0] ix, input [3:0] qx,
    input signed [12:0] wr, input signed [12:0] wj,
    input signed [12:0] wr_in_f, input signed [12:0] wj_in_f
  );
    automatic signed [3:0] ix_s = ix_s_fn(ix);
    automatic signed [3:0] qx_s = qx_s_fn(qx);
    automatic signed [12:0] wur = (mode==INT_W) ? wr     : wr_in_f;
    automatic signed [12:0] wuj = (mode==INT_W) ? wj     : wj_in_f;
    automatic signed [25:0] q1  = ($signed(qx_s) <<< M) + $signed((wuj*ix_s) - (wur*qx_s));
    automatic signed [4:0]  q2  = $signed(q1) >>> M;
    calc_qy = (mode==BYPASS || mode==CONT_W) ? qx_s : sat4(q2);
  endfunction

  function automatic signed [12:0] calc_wr_next(
    input [1:0] mode, input freeze,
    input signed [12:0] wr_prev,
    input signed [3:0]  iy_prev, input signed [3:0] qy_prev,
    input signed [12:0] wr_in_prev
  );
    if (mode==INT_W)      calc_wr_next = freeze ? wr_prev : $signed(wr_prev - ((iy_prev+qy_prev)*(iy_prev-qy_prev)));
    else if (mode==EXT_W) calc_wr_next = wr_in_prev;
    else                  calc_wr_next = '0;
  endfunction

  function automatic signed [12:0] calc_wj_next(
    input [1:0] mode, input freeze,
    input signed [12:0] wj_prev,
    input signed [3:0]  iy_prev, input signed [3:0] qy_prev,
    input signed [12:0] wj_in_prev
  );
    if (mode==INT_W)      calc_wj_next = freeze ? wj_prev : $signed(wj_prev - (2*iy_prev*qy_prev));
    else if (mode==EXT_W) calc_wj_next = wj_in_prev;
    else                  calc_wj_next = '0;
  endfunction

  default clocking cb @(posedge clk); endclocking
  default disable iff (!RESETn)

  // Basic correctness
  a_settled:    assert property (cb settled == freeze_iqcomp);
  a_reset_vals: assert property (cb !RESETn |-> (Iy==0 && Qy==0 && Wr==0 && Wj==0));
  a_range:      assert property (cb (Iy >= -8 && Iy <= 7) && (Qy >= -8 && Qy <= 7));
  a_no_x:       assert property (cb !$isunknown({op_mode, freeze_iqcomp, Ix, Qx, Wr_in, Wj_in, Iy, Qy, Wr, Wj, settled}));

  // Next-state functional equivalence (single concise checks cover all modes)
  a_Iy_next: assert property (cb 1'b1 |=> Iy == calc_iy($past(op_mode), $past(Ix), $past(Qx), $past(Wr), $past(Wj), $past(Wr_in), $past(Wj_in)));
  a_Qy_next: assert property (cb 1'b1 |=> Qy == calc_qy($past(op_mode), $past(Ix), $past(Qx), $past(Wr), $past(Wj), $past(Wr_in), $past(Wj_in)));
  a_W_next:  assert property (cb 1'b1 |=> (Wr == calc_wr_next($past(op_mode), $past(freeze_iqcomp), $past(Wr), $past(Iy), $past(Qy), $past(Wr_in)))
                                     && (Wj == calc_wj_next($past(op_mode), $past(freeze_iqcomp), $past(Wj), $past(Iy), $past(Qy), $past(Wj_in))));

  // Redundant but focused checks
  a_bypass_cont: assert property (cb (op_mode inside {BYPASS,CONT_W}) |=> (Iy == $signed($past(Ix) - 4'd8) && Qy == $signed($past(Qx) - 4'd8) && Wr==0 && Wj==0));
  a_extw_pass:   assert property (cb (op_mode==EXT_W) |=> (Wr==$past(Wr_in) && Wj==$past(Wj_in)));
  a_int_hold:    assert property (cb (op_mode==INT_W && freeze_iqcomp) |=> (Wr==$past(Wr) && Wj==$past(Wj)));
  a_int_upd:     assert property (cb (op_mode==INT_W && !freeze_iqcomp) |=> (Wr==$past(Wr) - (($past(Iy)+$past(Qy))*($past(Iy)-$past(Qy))))
                                                                     && (Wj==$past(Wj) - (2*$past(Iy)*$past(Qy))));

  // Coverage
  c_mode_bypass:  cover property (cb op_mode==BYPASS);
  c_mode_int:     cover property (cb op_mode==INT_W);
  c_mode_ext:     cover property (cb op_mode==EXT_W);
  c_mode_cont:    cover property (cb op_mode==CONT_W);

  c_int_hold:     cover property (cb (op_mode==INT_W && freeze_iqcomp) ##1 (Wr==$past(Wr) && Wj==$past(Wj)));
  c_int_upd:      cover property (cb (op_mode==INT_W && !freeze_iqcomp) ##1 (Wr!=$past(Wr) || Wj!=$past(Wj)));

  c_sat_I_pos:    cover property (cb (op_mode inside {INT_W,EXT_W}) ##1 (Iy==4'sd7));
  c_sat_I_neg:    cover property (cb (op_mode inside {INT_W,EXT_W}) ##1 (Iy==-4'sd8));
  c_sat_Q_pos:    cover property (cb (op_mode inside {INT_W,EXT_W}) ##1 (Qy==4'sd7));
  c_sat_Q_neg:    cover property (cb (op_mode inside {INT_W,EXT_W}) ##1 (Qy==-4'sd8));

  c_ext_passthru: cover property (cb (op_mode==EXT_W) ##1 (Wr==$past(Wr_in) && Wj==$past(Wj_in)));
  c_bypass_path:  cover property (cb (op_mode==BYPASS) ##1 (Iy==$signed($past(Ix)-4'd8) && Qy==$signed($past(Qx)-4'd8)));
endmodule