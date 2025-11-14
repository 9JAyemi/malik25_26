// SVA checker for mux8
module mux8_sva
  #(parameter int WIDTH=32, parameter int DISABLED=0)
  (input logic clk,
   input logic en,
   input logic [2:0] sel,
   input logic [WIDTH-1:0] i0,i1,i2,i3,i4,i5,i6,i7,
   input logic [WIDTH-1:0] o);

  default clocking cb @(posedge clk); endclocking

  // Consolidate inputs for concise properties
  logic [WIDTH-1:0] in[8];
  always_comb begin
    in[0]=i0; in[1]=i1; in[2]=i2; in[3]=i3;
    in[4]=i4; in[5]=i5; in[6]=i6; in[7]=i7;
  end

  // Determinism on control
  a_ctrl_known: assert property (!$isunknown({en,sel})) else $error("mux8: en/sel has X/Z");

  // Disabled path
  a_disabled:   assert property (!en |-> o == DISABLED) else $error("mux8: o must be DISABLED when en=0");

  // Functional mapping (single concise check)
  a_map:        assert property (en && !$isunknown(sel) |-> o == in[sel]) else $error("mux8: o != selected input");

  // No X on output when selected input and controls are known
  a_known_out:  assert property (en && !$isunknown({en,sel,in[sel]}) |-> !$isunknown(o)) else $error("mux8: o has X with known controls/data");

  // Stability: if selection and selected input are stable, o must be stable
  a_stable:     assert property (en && !$isunknown(sel) && $stable(sel) && $stable(in[sel]) |-> $stable(o)) else $error("mux8: o changed without selected input change");

  // Basic functional coverage
  genvar k;
  generate
    for (k=0; k<8; k++) begin : C
      c_sel_k: cover property (en && sel==k && o==in[k]);
    end
  endgenerate
  c_disabled: cover property (!en && o==DISABLED);
  c_sel_change: cover property (en && !$isunknown(sel) ##1 en && !$isunknown(sel) && sel != $past(sel));

endmodule

// Bind example (connect clk from your environment)
// bind mux8 mux8_sva #(.WIDTH(WIDTH), .DISABLED(DISABLED)))
//   mux8_sva_i(.clk(tb_clk), .en(en), .sel(sel),
//              .i0(i0), .i1(i1), .i2(i2), .i3(i3), .i4(i4), .i5(i5), .i6(i6), .i7(i7), .o(o));