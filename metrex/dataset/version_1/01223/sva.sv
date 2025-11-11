// SVA for 16:1 combinational multiplexer
// Bindable, concise, and focused on functional correctness and coverage.

`default_nettype none

module multiplexer_sva (
  input logic [5:0] in1,  in2,  in3,  in4,
                    in5,  in6,  in7,  in8,
                    in9,  in10, in11, in12,
                    in13, in14, in15, in16,
  input logic [3:0] sel,
  input logic [5:0] out
);

  function automatic logic [5:0] exp_out (input logic [3:0] s);
    case (s)
      4'h0:  exp_out = in1;
      4'h1:  exp_out = in2;
      4'h2:  exp_out = in3;
      4'h3:  exp_out = in4;
      4'h4:  exp_out = in5;
      4'h5:  exp_out = in6;
      4'h6:  exp_out = in7;
      4'h7:  exp_out = in8;
      4'h8:  exp_out = in9;
      4'h9:  exp_out = in10;
      4'hA:  exp_out = in11;
      4'hB:  exp_out = in12;
      4'hC:  exp_out = in13;
      4'hD:  exp_out = in14;
      4'hE:  exp_out = in15;
      4'hF:  exp_out = in16;
      default: exp_out = '0;
    endcase
  endfunction

  // Core functional assertion: out equals the selected input at all times
  always @* begin
    assert (out === exp_out(sel))
      else $error("MUX mismatch: sel=%0h out=%0h exp=%0h", sel, out, exp_out(sel));
  end

  // X/Z hygiene consistent with DUT default: if sel has any X/Z, out must be 0
  always @* begin
    if ($isunknown(sel)) assert (out === '0)
      else assert (!$isunknown(out) || $isunknown(exp_out(sel)));
  end

  // Functional coverage: every select value taken with correct mapping
  always @* begin
    cover (sel==4'h0  && out===in1);
    cover (sel==4'h1  && out===in2);
    cover (sel==4'h2  && out===in3);
    cover (sel==4'h3  && out===in4);
    cover (sel==4'h4  && out===in5);
    cover (sel==4'h5  && out===in6);
    cover (sel==4'h6  && out===in7);
    cover (sel==4'h7  && out===in8);
    cover (sel==4'h8  && out===in9);
    cover (sel==4'h9  && out===in10);
    cover (sel==4'hA  && out===in11);
    cover (sel==4'hB  && out===in12);
    cover (sel==4'hC  && out===in13);
    cover (sel==4'hD  && out===in14);
    cover (sel==4'hE  && out===in15);
    cover (sel==4'hF  && out===in16);
    cover ($isunknown(sel) && out==='0); // default branch exercised
  end

  // Propagation coverage: when sel is stable, changes on the selected input propagate to out
  always @* begin
    case (sel)
      4'h0:  cover ($stable(sel) && $changed(in1)  && $changed(out));
      4'h1:  cover ($stable(sel) && $changed(in2)  && $changed(out));
      4'h2:  cover ($stable(sel) && $changed(in3)  && $changed(out));
      4'h3:  cover ($stable(sel) && $changed(in4)  && $changed(out));
      4'h4:  cover ($stable(sel) && $changed(in5)  && $changed(out));
      4'h5:  cover ($stable(sel) && $changed(in6)  && $changed(out));
      4'h6:  cover ($stable(sel) && $changed(in7)  && $changed(out));
      4'h7:  cover ($stable(sel) && $changed(in8)  && $changed(out));
      4'h8:  cover ($stable(sel) && $changed(in9)  && $changed(out));
      4'h9:  cover ($stable(sel) && $changed(in10) && $changed(out));
      4'hA:  cover ($stable(sel) && $changed(in11) && $changed(out));
      4'hB:  cover ($stable(sel) && $changed(in12) && $changed(out));
      4'hC:  cover ($stable(sel) && $changed(in13) && $changed(out));
      4'hD:  cover ($stable(sel) && $changed(in14) && $changed(out));
      4'hE:  cover ($stable(sel) && $changed(in15) && $changed(out));
      4'hF:  cover ($stable(sel) && $changed(in16) && $changed(out));
    endcase
  end

endmodule

// Bind to DUT
bind multiplexer multiplexer_sva msva (.*);

`default_nettype wire