// SVA binder for mux_6to1
module mux_6to1_sva (
  input logic [2:0] sel,
  input logic [3:0] in0,
  input logic [3:0] in1,
  input logic [3:0] in2,
  input logic [3:0] in3,
  input logic [3:0] in4,
  input logic [3:0] in5,
  input logic [3:0] out
);

  function automatic logic [3:0] exp_out (
    input logic [2:0] s,
    input logic [3:0] i0,i1,i2,i3,i4,i5
  );
    case (s)
      3'd0: exp_out = i0;
      3'd1: exp_out = i1;
      3'd2: exp_out = i2;
      3'd3: exp_out = i3;
      3'd4: exp_out = i4;
      3'd5: exp_out = i5;
      default: exp_out = 4'b0000;
    endcase
  endfunction

  logic [3:0] exp_o;
  always_comb exp_o = exp_out(sel, in0, in1, in2, in3, in4, in5);

  // Combinational functional equivalence
  always @* begin
    assert (out === exp_o)
      else $error("mux_6to1 mismatch: sel=%0d out=%b exp=%b", sel, out, exp_o);

    // No unexpected X/Z propagation when inputs and select are known
    if (!$isunknown(sel) && !$isunknown(exp_o)) begin
      assert (!$isunknown(out))
        else $error("mux_6to1 X/Z on out with known sel/inputs: sel=%0d exp=%b out=%b", sel, exp_o, out);
    end

    // Output change coherence with expected output
    assert ($changed(out) == $changed(exp_o))
      else $error("mux_6to1 out change not coherent with expected output");
  end

  // Minimal functional coverage
  always @* begin
    cover (sel==3'd0 && out===in0);
    cover (sel==3'd1 && out===in1);
    cover (sel==3'd2 && out===in2);
    cover (sel==3'd3 && out===in3);
    cover (sel==3'd4 && out===in4);
    cover (sel==3'd5 && out===in5);
    cover ((sel==3'd6 || sel==3'd7) && out===4'b0000);

    // Observe out reflecting selected input activity
    cover (sel==3'd0 && $changed(in0) && $changed(out));
    cover (sel==3'd1 && $changed(in1) && $changed(out));
    cover (sel==3'd2 && $changed(in2) && $changed(out));
    cover (sel==3'd3 && $changed(in3) && $changed(out));
    cover (sel==3'd4 && $changed(in4) && $changed(out));
    cover (sel==3'd5 && $changed(in5) && $changed(out));

    // Exercise select changes
    cover ($changed(sel));
  end

endmodule

bind mux_6to1 mux_6to1_sva u_mux_6to1_sva (.*);