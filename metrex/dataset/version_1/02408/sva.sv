// SVA for top_module (bind to DUT)
module top_module_sva
(
  input logic        Clk,
  input logic        reset,
  input logic [3:0]  a,
  input logic [3:0]  b,
  input logic        gt,
  input logic        lt,
  input logic        eq,
  input logic [7:0]  johnson_out,
  input logic [2:0]  comp_out
);

  default clocking cb @(posedge Clk); endclocking

  // Comparator encoding and sanity
  assert property ( (comp_out[2] == (a > b)) && (comp_out[1] == (a < b)) && (comp_out[0] == (a == b)) );
  assert property ( (comp_out[2] + comp_out[1] + comp_out[0]) == 1 );

  // Reset behavior (post-NBA check)
  assert property ( reset |-> ##0 (gt==0 && lt==0 && eq==0 && johnson_out==8'h01) );

  // No X after update when not in reset
  assert property ( !reset |-> ##0 !$isunknown({gt,lt,eq,johnson_out,comp_out}) );

  // Output decode per comp_out (post-NBA)
  assert property ( disable iff (reset) (comp_out==3'b000) |-> ##0 (gt==0 && lt==0 && eq==0) );
  assert property ( disable iff (reset) (comp_out==3'b001) |-> ##0 (gt==0 && lt==0 && eq==1) );
  assert property ( disable iff (reset) (comp_out==3'b010) |-> ##0 (gt==1 && lt==0 && eq==0) );
  assert property ( disable iff (reset) (comp_out==3'b011) |-> ##0 (gt==1 && lt==0 && eq==1) );
  assert property ( disable iff (reset) (comp_out==3'b100) |-> ##0 (gt==0 && lt==1 && eq==0) );
  assert property ( disable iff (reset) (comp_out==3'b101) |-> ##0 (gt==0 && lt==1 && eq==1) );
  assert property ( disable iff (reset) (comp_out==3'b110) |-> ##0 (gt==1 && lt==1 && eq==0) );
  assert property ( disable iff (reset) (comp_out==3'b111) |-> ##0 (gt==1 && lt==1 && eq==1) );

  // Johnson counter: one-hot and shift/wrap
  assert property ( $onehot(johnson_out) ); // also holds on reset cycle due to reset assignment
  assert property ( disable iff (reset) ($past(!reset) && $past(johnson_out)!=8'h80) |-> (johnson_out == ($past(johnson_out) << 1)) );
  assert property ( disable iff (reset) ($past(!reset) && $past(johnson_out)==8'h80) |-> (johnson_out == 8'h01) );

  // Coverage
  cover property ( disable iff (reset) comp_out==3'b000 );
  cover property ( disable iff (reset) comp_out==3'b001 );
  cover property ( disable iff (reset) comp_out==3'b010 );
  cover property ( disable iff (reset) comp_out==3'b011 );
  cover property ( disable iff (reset) comp_out==3'b100 );
  cover property ( disable iff (reset) comp_out==3'b101 );
  cover property ( disable iff (reset) comp_out==3'b110 );
  cover property ( disable iff (reset) comp_out==3'b111 );

  cover property ( disable iff (reset)
    (johnson_out==8'h01) ##1 (johnson_out==8'h02) ##1 (johnson_out==8'h04) ##1 (johnson_out==8'h08) ##
    1 (johnson_out==8'h10) ##1 (johnson_out==8'h20) ##1 (johnson_out==8'h40) ##1 (johnson_out==8'h80) ##
    1 (johnson_out==8'h01) );

endmodule

bind top_module top_module_sva top_module_sva_i (.*);