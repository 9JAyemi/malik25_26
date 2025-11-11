// SVA for priority_mux
// Bind example (connect a sampling clock from your env):
//   bind priority_mux priority_mux_sva u_sva(.clk(tb_clk), .in(in), .out(out), .select(select));

module priority_mux_sva (
  input logic              clk,
  input logic [3:0]        in,
  input logic              out,
  input logic [1:0]        select
);

  default clocking @(posedge clk); endclocking

  // Input-clean => no X on internal select and out
  assert property ( !$isunknown(in) |-> !$isunknown(select) );
  assert property ( !$isunknown({in,select}) |-> !$isunknown(out) );

  // Decode correctness (select generation)
  assert property ( (!$isunknown(in) && (in==4'b0010)) |=> (select==2'b01) );
  assert property ( (!$isunknown(in) && (in==4'b0100)) |=> (select==2'b10) );
  assert property ( (!$isunknown(in) && (in==4'b1000)) |=> (select==2'b11) );
  assert property ( (!$isunknown(in) && !(in inside {4'b0010,4'b0100,4'b1000})) |=> (select==2'b00) );

  // Mux correctness (out must reflect selected bit)
  assert property ( (!$isunknown({in,select})) |=> 
                    ( out == (select==2'b00 ? in[0] :
                              select==2'b01 ? in[1] :
                              select==2'b10 ? in[2] :
                                              in[3]) ) );

  // End-to-end functional equivalence (concise spec of the DUT behavior)
  // Out is in[0] except when in is exactly 0010/0100/1000, where out is 1
  assert property ( !$isunknown(in) |=> 
                    out == ( in[0] | (in==4'b0010) | (in==4'b0100) | (in==4'b1000) ) );

  // Covers (functional stimulus/observability)
  cover property ( in==4'b0000 && select==2'b00 && out==1'b0 );
  cover property ( in==4'b0001 && select==2'b00 && out==in[0] );
  cover property ( in==4'b0010 && select==2'b01 && out==in[1] );
  cover property ( in==4'b0100 && select==2'b10 && out==in[2] );
  cover property ( in==4'b1000 && select==2'b11 && out==in[3] );
  cover property ( in==4'b0011 && select==2'b00 && out==in[0] ); // multi-hot -> default path
  cover property ( $changed(out) ); // observe output activity

endmodule