// SVA for sp_mux_5to1_sel3_4_1
// Concise, high-quality checks + coverage. Bind into DUT.
// Assumes pure combinational behavior; uses @(*) clocking.

`ifndef SYNTHESIS

module sp_mux_5to1_sel3_4_1_sva (
  input  [3:0] din1,
  input  [3:0] din2,
  input  [3:0] din3,
  input  [3:0] din4,
  input  [3:0] din5,
  input  [2:0] din6,  // sel
  output [3:0] dout
);

  default clocking cb @(*); endclocking

  // Basic X/Z control checks
  a_no_x_on_sel:        assert property (!$isunknown(din6))
    else $error("sel (din6) contains X/Z");

  // Functional mapping checks (4-state equality)
  a_sel_1xx_is_din5:    assert property (din6[2] |-> (dout === din5))
    else $error("When sel[2]=1, dout must equal din5");

  a_sel_000_is_din1:    assert property ((din6 == 3'b000) |-> (dout === din1))
    else $error("sel=000 -> dout!=din1");
  a_sel_001_is_din2:    assert property ((din6 == 3'b001) |-> (dout === din2))
    else $error("sel=001 -> dout!=din2");
  a_sel_010_is_din3:    assert property ((din6 == 3'b010) |-> (dout === din3))
    else $error("sel=010 -> dout!=din3");
  a_sel_011_is_din4:    assert property ((din6 == 3'b011) |-> (dout === din4))
    else $error("sel=011 -> dout!=din4");

  // Known-value propagation when selected input is known
  a_known_000:          assert property ((din6 == 3'b000 && !$isunknown(din1)) |-> !$isunknown(dout))
    else $error("Known din1 did not produce known dout");
  a_known_001:          assert property ((din6 == 3'b001 && !$isunknown(din2)) |-> !$isunknown(dout))
    else $error("Known din2 did not produce known dout");
  a_known_010:          assert property ((din6 == 3'b010 && !$isunknown(din3)) |-> !$isunknown(dout))
    else $error("Known din3 did not produce known dout");
  a_known_011:          assert property ((din6 == 3'b011 && !$isunknown(din4)) |-> !$isunknown(dout))
    else $error("Known din4 did not produce known dout");
  a_known_1xx:          assert property ((din6[2] && !$isunknown(din5)) |-> !$isunknown(dout))
    else $error("Known din5 did not produce known dout when sel[2]=1");

  // Functional coverage: hit every selection path
  c_sel_000:            cover property (din6 == 3'b000 && (dout === din1));
  c_sel_001:            cover property (din6 == 3'b001 && (dout === din2));
  c_sel_010:            cover property (din6 == 3'b010 && (dout === din3));
  c_sel_011:            cover property (din6 == 3'b011 && (dout === din4));
  c_sel_1xx:            cover property (din6[2] && (dout === din5));

endmodule

bind sp_mux_5to1_sel3_4_1 sp_mux_5to1_sel3_4_1_sva u_sp_mux_5to1_sel3_4_1_sva (.*);

`endif