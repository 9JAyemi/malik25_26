// SVA for sp_mux_4to1_sel2_7_1
module sp_mux_4to1_sel2_7_1_sva (
  input logic [6:0] din1,
  input logic [6:0] din2,
  input logic [6:0] din3,
  input logic [6:0] din4,
  input logic [1:0] din5,
  input logic [6:0] dout
);
  default clocking cb @(posedge $global_clock); endclocking

  // Functional correctness (all 4 select cases)
  assert property (din5 == 2'b00 |-> dout === din1);
  assert property (din5 == 2'b01 |-> dout === din2);
  assert property (din5 == 2'b10 |-> dout === din3);
  assert property (din5 == 2'b11 |-> dout === din4);

  // No-X on output when select and selected input are known
  assert property ((!$isunknown(din5) && (din5==2'b00) && !$isunknown(din1)) |-> dout === din1);
  assert property ((!$isunknown(din5) && (din5==2'b01) && !$isunknown(din2)) |-> dout === din2);
  assert property ((!$isunknown(din5) && (din5==2'b10) && !$isunknown(din3)) |-> dout === din3);
  assert property ((!$isunknown(din5) && (din5==2'b11) && !$isunknown(din4)) |-> dout === din4);

  // Basic functional coverage: each select value seen and propagated
  cover property (din5 == 2'b00 && dout === din1);
  cover property (din5 == 2'b01 && dout === din2);
  cover property (din5 == 2'b10 && dout === din3);
  cover property (din5 == 2'b11 && dout === din4);

  // Transition coverage: select changes cause corresponding output update
  cover property ($changed(din5) && !$isunknown(din5) ##0
                  ((din5==2'b00 && dout===din1) ||
                   (din5==2'b01 && dout===din2) ||
                   (din5==2'b10 && dout===din3) ||
                   (din5==2'b11 && dout===din4)));

  // Bit-level select toggles
  cover property ($rose(din5[0]));  cover property ($fell(din5[0]));
  cover property ($rose(din5[1]));  cover property ($fell(din5[1]));
endmodule

bind sp_mux_4to1_sel2_7_1 sp_mux_4to1_sel2_7_1_sva sva_i (.*);