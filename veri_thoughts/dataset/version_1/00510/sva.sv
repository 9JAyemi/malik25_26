// SVA for sp_mux_9to1_sel4_6_1
// Bind-friendly, combinational, concise, full functional coverage

module sp_mux_9to1_sel4_6_1_sva (
  input  logic [5:0] din1,
  input  logic [5:0] din2,
  input  logic [5:0] din3,
  input  logic [5:0] din4,
  input  logic [5:0] din5,
  input  logic [5:0] din6,
  input  logic [5:0] din7,
  input  logic [5:0] din8,
  input  logic [5:0] din9,
  input  logic [3:0] din10,
  input  logic [5:0] dout
);
  // Static sanity
  initial assert ($bits(dout) == $bits(din1));

  // Use input activity as the SVA clock
  default clocking cb @(din1 or din2 or din3 or din4 or din5 or din6 or din7 or din8 or din9 or din10 or dout); endclocking

  logic [3:0] sel;
  assign sel = din10;

  // Core functional assertions
  // sel[3]==1 picks din9
  assert property ( sel[3] |-> (dout == din9) );

  // sel[3]==0 selects among din1..din8 via sel[2:0]
  assert property ( !sel[3] && !sel[2] && !sel[1] |-> (dout == (sel[0] ? din2 : din1)) );
  assert property ( !sel[3] && !sel[2] &&  sel[1] |-> (dout == (sel[0] ? din4 : din3)) );
  assert property ( !sel[3] &&  sel[2] && !sel[1] |-> (dout == (sel[0] ? din6 : din5)) );
  assert property ( !sel[3] &&  sel[2] &&  sel[1] |-> (dout == (sel[0] ? din8 : din7)) );

  // Minimal X-safety on selected path
  assert property ( (! $isunknown(sel) && sel[3] && ! $isunknown(din9)) |-> ! $isunknown(dout) );
  assert property ( (! $isunknown(sel) && !sel[3] && !sel[2] && !sel[1] &&
                     ! $isunknown(sel[0] ? din2 : din1)) |-> ! $isunknown(dout) );
  assert property ( (! $isunknown(sel) && !sel[3] && !sel[2] &&  sel[1] &&
                     ! $isunknown(sel[0] ? din4 : din3)) |-> ! $isunknown(dout) );
  assert property ( (! $isunknown(sel) && !sel[3] &&  sel[2] && !sel[1] &&
                     ! $isunknown(sel[0] ? din6 : din5)) |-> ! $isunknown(dout) );
  assert property ( (! $isunknown(sel) && !sel[3] &&  sel[2] &&  sel[1] &&
                     ! $isunknown(sel[0] ? din8 : din7)) |-> ! $isunknown(dout) );

  // Functional coverage: exercise all 9 selections
  cover property ( sel[3] );                                   // din9 selected
  cover property ( !sel[3] && !sel[2] && !sel[1] && !sel[0] ); // din1
  cover property ( !sel[3] && !sel[2] && !sel[1] &&  sel[0] ); // din2
  cover property ( !sel[3] && !sel[2] &&  sel[1] && !sel[0] ); // din3
  cover property ( !sel[3] && !sel[2] &&  sel[1] &&  sel[0] ); // din4
  cover property ( !sel[3] &&  sel[2] && !sel[1] && !sel[0] ); // din5
  cover property ( !sel[3] &&  sel[2] && !sel[1] &&  sel[0] ); // din6
  cover property ( !sel[3] &&  sel[2] &&  sel[1] && !sel[0] ); // din7
  cover property ( !sel[3] &&  sel[2] &&  sel[1] &&  sel[0] ); // din8
endmodule

// Bind into the DUT (instantiate once in your testbench or a package)
bind sp_mux_9to1_sel4_6_1 sp_mux_9to1_sel4_6_1_sva i_sp_mux_9to1_sel4_6_1_sva (
  .din1(din1), .din2(din2), .din3(din3), .din4(din4),
  .din5(din5), .din6(din6), .din7(din7), .din8(din8),
  .din9(din9), .din10(din10), .dout(dout)
);