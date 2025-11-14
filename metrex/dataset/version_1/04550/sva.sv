// SVA checker for alu
module alu_sva #(parameter W=16) (
  input logic [W-1:0] x,
  input logic [W-1:0] y,
  input logic zx, nx, zy, ny, f, no,
  input logic [W-1:0] out,
  input logic zr,
  input logic ng
);

  function automatic logic [W-1:0] golden_out(
    input logic [W-1:0] x, y,
    input logic zx, nx, zy, ny, f, no
  );
    logic [W-1:0] ax, ay, o;
    ax = zx ? '0 : x;
    ax = nx ? ~ax : ax;
    ay = zy ? '0 : y;
    ay = ny ? ~ay : ay;
    o  = f  ? (ax + ay) : (ax & ay);
    golden_out = no ? ~o : o;
  endfunction

  event comb_ev = (x or y or zx or nx or zy or ny or f or no);

  // Functional correctness of out
  property p_out_correct;
    @(comb_ev) disable iff ($isunknown({x,y,zx,nx,zy,ny,f,no}))
      1'b1 |-> ##0 (out == golden_out(x,y,zx,nx,zy,ny,f,no));
  endproperty
  assert property (p_out_correct);

  // Flags correctness
  property p_flags_correct;
    @(comb_ev) disable iff ($isunknown({x,y,zx,nx,zy,ny,f,no}))
      ##0 ((zr == (out == '0)) && (ng == out[W-1]));
  endproperty
  assert property (p_flags_correct);

  // No X/Z on outputs when inputs are known
  property p_no_xz_outputs;
    @(comb_ev) disable iff ($isunknown({x,y,zx,nx,zy,ny,f,no}))
      ##0 !$isunknown({out,zr,ng});
  endproperty
  assert property (p_no_xz_outputs);

  // Coverage: exercise control space and key outcomes
  cover property (@(comb_ev) ##0 zx);
  cover property (@(comb_ev) ##0 !zx);
  cover property (@(comb_ev) ##0 nx);
  cover property (@(comb_ev) ##0 !nx);
  cover property (@(comb_ev) ##0 zy);
  cover property (@(comb_ev) ##0 !zy);
  cover property (@(comb_ev) ##0 ny);
  cover property (@(comb_ev) ##0 !ny);
  cover property (@(comb_ev) ##0 f);
  cover property (@(comb_ev) ##0 !f);
  cover property (@(comb_ev) ##0 no);
  cover property (@(comb_ev) ##0 !no);

  cover property (@(comb_ev) disable iff ($isunknown({x,y,zx,nx,zy,ny,f,no})) ##0 (out == '0) && zr && !ng);
  cover property (@(comb_ev) disable iff ($isunknown({x,y,zx,nx,zy,ny,f,no})) ##0 (out[W-1]) && ng);
  cover property (@(comb_ev) disable iff ($isunknown({x,y,zx,nx,zy,ny,f,no})) ##0 (out == '1));

  cover property (@(comb_ev) disable iff ($isunknown({x,y,zx,nx,zy,ny,f,no})) ##0 (f==0 && no==0));
  cover property (@(comb_ev) disable iff ($isunknown({x,y,zx,nx,zy,ny,f,no})) ##0 (f==0 && no==1));
  cover property (@(comb_ev) disable iff ($isunknown({x,y,zx,nx,zy,ny,f,no})) ##0 (f==1 && no==0));
  cover property (@(comb_ev) disable iff ($isunknown({x,y,zx,nx,zy,ny,f,no})) ##0 (f==1 && no==1));
  cover property (@(comb_ev) disable iff ($isunknown({x,y,zx,nx,zy,ny,f,no})) ##0 (zx || zy));
  cover property (@(comb_ev) disable iff ($isunknown({x,y,zx,nx,zy,ny,f,no})) ##0 (nx || ny));

endmodule

// Bind to all alu instances
bind alu alu_sva #(.W(16)) alu_sva_i (.*);