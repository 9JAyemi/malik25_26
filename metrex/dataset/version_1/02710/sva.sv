// SVA for mux4: concise, high-quality checks and coverage.
// Choose either the clocked checker (preferred for concurrent SVA)
// or the clockless immediate-assert checker for purely combinational contexts.

// Clocked concurrent SVA checker (bind to an external clock/reset if available)
module mux4_sva_chk #(
  parameter bit HAS_RSTN = 0  // 1 if rst_n is provided, 0 to ignore reset
) (
  input  logic        clk,
  input  logic        rst_n,
  input  logic [3:0]  in0,
  input  logic [3:0]  in1,
  input  logic [3:0]  in2,
  input  logic [3:0]  in3,
  input  logic [1:0]  sel,
  input  logic [3:0]  out
);
  default clocking cb @(posedge clk); endclocking

  // X/Z hygiene on key controls/outputs
  ap_sel_known: assert property (disable iff (HAS_RSTN && !rst_n) !$isunknown(sel))
    else $error("mux4: sel contains X/Z");

  ap_out_known: assert property (disable iff (HAS_RSTN && !rst_n) !$isunknown(out))
    else $error("mux4: out contains X/Z");

  // Functional correctness: out equals selected input
  ap_mux_func: assert property (disable iff (HAS_RSTN && !rst_n)
    out == (sel==2'b00 ? in0 :
            sel==2'b01 ? in1 :
            sel==2'b10 ? in2 : in3))
    else $error("mux4: functional mismatch for sel=%0b", sel);

  // Stability: if selection and selected input are stable, out stays stable
  ap_hold_when_stable: assert property (disable iff (HAS_RSTN && !rst_n)
    $stable(sel) &&
    ((sel==2'b00 && $stable(in0)) ||
     (sel==2'b01 && $stable(in1)) ||
     (sel==2'b10 && $stable(in2)) ||
     (sel==2'b11 && $stable(in3)))
    |=> $stable(out))
    else $error("mux4: out changed despite stable select/data");

  // Functional coverage (concise, complete)
  cv_sel_00: cover property (sel==2'b00);
  cv_sel_01: cover property (sel==2'b01);
  cv_sel_10: cover property (sel==2'b10);
  cv_sel_11: cover property (sel==2'b11);

  cv_route0: cover property (sel==2'b00 && out==in0);
  cv_route1: cover property (sel==2'b01 && out==in1);
  cv_route2: cover property (sel==2'b10 && out==in2);
  cv_route3: cover property (sel==2'b11 && out==in3);

  cv_sel_change: cover property ($changed(sel));
  cv_out_change: cover property ($changed(out));

endmodule

// Optional: Clockless immediate-assert checker for pure combinational use
module mux4_sva_comb (
  input  logic [3:0]  in0,
  input  logic [3:0]  in1,
  input  logic [3:0]  in2,
  input  logic [3:0]  in3,
  input  logic [1:0]  sel,
  input  logic [3:0]  out
);
  always_comb begin
    assert (!$isunknown(sel)) else $error("mux4: sel contains X/Z");
    unique case (sel)
      2'b00: assert (out === in0) else $error("mux4: out!=in0 when sel=00");
      2'b01: assert (out === in1) else $error("mux4: out!=in1 when sel=01");
      2'b10: assert (out === in2) else $error("mux4: out!=in2 when sel=10");
      2'b11: assert (out === in3) else $error("mux4: out!=in3 when sel=11");
    endcase
    assert (!$isunknown(out)) else $error("mux4: out contains X/Z");
  end
endmodule

// Example binds (uncomment and adapt):
// bind mux4 mux4_sva_chk #(.HAS_RSTN(0)) u_mux4_sva_chk (.* , .clk(tb_clk), .rst_n(1'b1));
// or, without a clock:
// bind mux4 mux4_sva_comb u_mux4_sva_comb (.*);