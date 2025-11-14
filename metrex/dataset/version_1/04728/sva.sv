// SVA for mux_256to1
// Concise, full functional checking and practical coverage

module mux_256to1_sva (
  input logic [255:0] in,
  input logic [7:0]   sel,
  input logic         out
);

  // Functional equivalence (combinational)
  a_func: assert property (@(in or sel or out)
                           out === (sel[7] ? in[sel[6:0]] : 1'b0))
          else $error("mux_256to1 func mismatch: sel=%0h idx=%0d out=%b exp=%b",
                      sel, sel[6:0], out, (sel[7] ? in[sel[6:0]] : 1'b0));

  // Branch checks
  a_gate0: assert property (@(in or sel or out) (sel[7]===1'b0) |-> (out===1'b0))
           else $error("mux_256to1: out not 0 when sel[7]==0");

  a_gate1: assert property (@(in or sel or out) (sel[7]===1'b1) |-> (out===in[sel[6:0]]))
           else $error("mux_256to1: out!=in[idx] when sel[7]==1");

  // X-prop sanity: when driving inputs are known, out must be known
  a_known0: assert property (@(in or sel or out) (sel[7]===1'b0) |-> !$isunknown(out))
            else $error("mux_256to1: out X/Z with sel[7]==0");

  a_known1: assert property (@(in or sel or out)
                             (sel[7]===1'b1 && !$isunknown(sel[6:0]) && !$isunknown(in[sel[6:0]]))
                             |-> (!$isunknown(out) && out===in[sel[6:0]]))
            else $error("mux_256to1: out not known/eq when selected input known");

  // Dynamic pass-through (zero-delay) and isolation when sel is stable
  a_follow: assert property (@(in or sel or out)
                             (sel[7]===1'b1 && $stable(sel) && $changed(in[sel[6:0]]))
                             |-> ##0 ($changed(out) && out===in[sel[6:0]]))
            else $error("mux_256to1: out did not follow selected input change");

  a_isolate: assert property (@(in or sel or out)
                              (sel[7]===1'b1 && $stable(sel) && $stable(in[sel[6:0]]))
                              |-> ##0 $stable(out))
             else $error("mux_256to1: out changed without selected input change");

  // Coverage: both branches
  c_sel0:  cover property (@(in or sel or out) sel[7]===1'b0);
  c_sel1:  cover property (@(in or sel or out) sel[7]===1'b1);

  // Coverage: index space actually used by the RTL (0..127)
  genvar i;
  generate
    for (i=0; i<128; i++) begin : GEN_COV_IDX
      c_idx: cover property (@(in or sel or out) sel[7] && sel[6:0]==i);
    end
  endgenerate

  // Edge index coverage
  c_idx0:   cover property (@(in or sel or out) sel[7] && sel[6:0]==7'd0);
  c_idx127: cover property (@(in or sel or out) sel[7] && sel[6:0]==7'd127);

endmodule

bind mux_256to1 mux_256to1_sva sva(.in(in), .sel(sel), .out(out));