// SVA for sky130_fd_sc_ms__a222oi (Y = ~((A1&A2)|(B1&B2)|(C1&C2)))
// Bindable checker + bind

checker a222oi_sva (
  input logic Y,
  input logic A1, A2, B1, B2, C1, C2,
  input logic nand0_out, nand1_out, nand2_out, and0_out_Y
);
  // Sample on any input edge
  default clocking cb @(
    posedge A1 or negedge A1 or
    posedge A2 or negedge A2 or
    posedge B1 or negedge B1 or
    posedge B2 or negedge B2 or
    posedge C1 or negedge C1 or
    posedge C2 or negedge C2
  ); endclocking

  // Functional truth assertion (AOI222)
  a_func: assert property (1 |-> ##0 (Y === ~((A1 & A2) | (B1 & B2) | (C1 & C2))));

  // Structural consistency
  a_n0:  assert property (1 |-> ##0 (nand0_out  === ~(A1 & A2)));
  a_n1:  assert property (1 |-> ##0 (nand1_out  === ~(B1 & B2)));
  a_n2:  assert property (1 |-> ##0 (nand2_out  === ~(C1 & C2)));
  a_and: assert property (1 |-> ##0 (and0_out_Y === (nand0_out & nand1_out & nand2_out)));
  a_buf: assert property (1 |-> ##0 (Y === and0_out_Y));

  // Known-propagation: known inputs -> known internal nodes and output
  a_known: assert property (
    (!$isunknown({A1,A2,B1,B2,C1,C2})) |-> ##0 (!$isunknown({nand0_out,nand1_out,nand2_out,and0_out_Y,Y}))
  );

  // Minimal, meaningful coverage
  // Output states
  c_y1: cover property (!(A1 & A2) && !(B1 & B2) && !(C1 & C2) ##0 (Y == 1));
  c_y0: cover property ( (A1 & A2) ||  (B1 & B2) ||  (C1 & C2) ##0 (Y == 0));

  // Each pair independently forces Y low
  c_A_forces0: cover property ( (A1 & A2) && !(B1 & B2) && !(C1 & C2) ##0 (Y == 0));
  c_B_forces0: cover property (!(A1 & A2) &&  (B1 & B2) && !(C1 & C2) ##0 (Y == 0));
  c_C_forces0: cover property (!(A1 & A2) && !(B1 & B2) &&  (C1 & C2) ##0 (Y == 0));

  // Input toggle coverage (both edges)
  c_A1_r: cover property (@(posedge A1) 1);
  c_A1_f: cover property (@(negedge A1) 1);
  c_A2_r: cover property (@(posedge A2) 1);
  c_A2_f: cover property (@(negedge A2) 1);
  c_B1_r: cover property (@(posedge B1) 1);
  c_B1_f: cover property (@(negedge B1) 1);
  c_B2_r: cover property (@(posedge B2) 1);
  c_B2_f: cover property (@(negedge B2) 1);
  c_C1_r: cover property (@(posedge C1) 1);
  c_C1_f: cover property (@(negedge C1) 1);
  c_C2_r: cover property (@(posedge C2) 1);
  c_C2_f: cover property (@(negedge C2) 1);
endchecker

bind sky130_fd_sc_ms__a222oi a222oi_sva a222oi_sva_i (.*);