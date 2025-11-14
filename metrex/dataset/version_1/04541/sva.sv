// SVA for sky130_fd_sc_lp__o22a: X = (A1 | A2) & (B1 | B2)
module sky130_fd_sc_lp__o22a_sva
(
  input logic A1, A2, B1, B2,
  input logic X,
  input logic or0_out, or1_out, and0_out_X
);
  // Combinational correctness (delta-cycle safe)
  always_comb begin
    assert (#0 (or0_out    === (A1 || A2))) else $error("o22a: or0_out != (A1||A2)");
    assert (#0 (or1_out    === (B1 || B2))) else $error("o22a: or1_out != (B1||B2)");
    assert (#0 (and0_out_X === (or0_out && or1_out))) else $error("o22a: and0_out_X != (or0_out&&or1_out)");
    assert (#0 (X          ===  and0_out_X)) else $error("o22a: X != and0_out_X (buf)");
    assert (#0 (X          === ((A1 || A2) && (B1 || B2)))) else $error("o22a: X != (A|A2)&(B|B2)");
    if (!$isunknown({A1,A2,B1,B2})) assert (#0 !$isunknown(X)) else $error("o22a: X unknown while inputs known");
  end

  // Toggle coverage on all pins
  cover property (@(posedge A1) 1);
  cover property (@(negedge A1) 1);
  cover property (@(posedge A2) 1);
  cover property (@(negedge A2) 1);
  cover property (@(posedge B1) 1);
  cover property (@(negedge B1) 1);
  cover property (@(posedge B2) 1);
  cover property (@(negedge B2) 1);
  cover property (@(posedge X)  1);
  cover property (@(negedge X)  1);

  // Functional coverage of X outcomes and causes
  cover property (@(A1 or A2 or B1 or B2 or X) X == 1);
  cover property (@(A1 or A2 or B1 or B2 or X) X == 0);
  // X==1 via each contributing pair
  cover property (@(A1 or A2 or B1 or B2 or X) (A1 && B1) && (X==1));
  cover property (@(A1 or A2 or B1 or B2 or X) (A1 && B2) && (X==1));
  cover property (@(A1 or A2 or B1 or B2 or X) (A2 && B1) && (X==1));
  cover property (@(A1 or A2 or B1 or B2 or X) (A2 && B2) && (X==1));
  // X==0 because one OR-group is 0
  cover property (@(A1 or A2 or B1 or B2 or X) (!A1 && !A2) && (B1 || B2) && (X==0));
  cover property (@(A1 or A2 or B1 or B2 or X) (!B1 && !B2) && (A1 || A2) && (X==0));

  // Optional compact coverage of all 16 input combinations
  genvar v;
  generate
    for (v=0; v<16; v++) begin : g_all_inputs
      cover property (@(A1 or A2 or B1 or B2 or X) {A1,A2,B1,B2} == v[3:0]);
    end
  endgenerate
endmodule

// Bind to DUT (connect internal nets for deeper checking)
bind sky130_fd_sc_lp__o22a sky130_fd_sc_lp__o22a_sva
  u_o22a_sva (
    .A1(A1), .A2(A2), .B1(B1), .B2(B2), .X(X),
    .or0_out(or0_out), .or1_out(or1_out), .and0_out_X(and0_out_X)
  );