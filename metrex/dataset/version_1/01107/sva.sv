// SVA checker for bin2gray. Bind this to the DUT.
module bin2gray_sva (
  input logic        clk,
  input logic [3:0]  bin,
  input logic [3:0]  gray,
  input logic        valid,
  input logic [3:0]  prev_gray
);

  // past-sample enables (no explicit reset in DUT)
  logic past1, past2;
  initial begin past1 = 1'b0; past2 = 1'b0; end
  always_ff @(posedge clk) begin
    past1 <= 1'b1;
    past2 <= past1;
  end

  function automatic logic [3:0] f_bin2gray (input logic [3:0] b);
    return { b[3], b[3]^b[2], b[2]^b[1], b[1]^b[0] };
  endfunction

  default clocking cb @ (posedge clk); endclocking
  default disable iff (!past1);

  // Functional mapping: registered output equals function of previous-cycle input
  assert property (gray == f_bin2gray($past(bin)));

  // Input/output coupling (bijective map): stability and change
  assert property ((bin == $past(bin)) |-> (gray == $past(gray)));
  assert property ((bin != $past(bin)) |-> (gray != $past(gray)));

  // prev_gray must hold previous cycle's gray
  assert property (prev_gray == $past(gray));

  // valid semantics as implemented: 1 iff gray changed between t-2 and t-1
  assert property (past2 |-> (valid == ($past(gray,1) != $past(gray,2))));
  assert property (past2 && ($past(gray,1) == $past(gray,2)) |-> !valid);
  assert property (valid |-> past2 && ($past(gray,1) != $past(gray,2)));

  // Coverage
  cover property (gray == f_bin2gray($past(bin)));
  cover property (past2 && (bin != $past(bin)) ##1 valid);
  cover property (past2 && (bin == $past(bin)) ##1 !valid);

  // Input space coverage (all 16 codes seen)
  covergroup cg_inputs @ (posedge clk);
    cp_bin: coverpoint bin { bins all[] = {[0:15]}; }
  endgroup
  cg_inputs cg_inputs_i = new();

endmodule

bind bin2gray bin2gray_sva b2g_sva (.*);