// SVA for add_sub_4bit
// Concise, bound, combinationally triggered, with core checks and focused coverage

`ifndef ADD_SUB_4BIT_SVA_SV
`define ADD_SUB_4BIT_SVA_SV

module add_sub_4bit_sva (add_sub_4bit dut);

  // Fire assertions on any input change; sample after a delta (##0) to avoid races
  event ev;
  always @(dut.A or dut.B or dut.mode) -> ev;

  default clocking cb @(ev); endclocking

  function automatic [4:0] exp_sum (input logic [3:0] a, input logic [3:0] b, input logic mode);
    exp_sum = {1'b0, a} + (mode ? ({1'b0, ~b} + 5'd1) : {1'b0, b});
  endfunction

  // Core functional correctness
  assert property (##0 {dut.COUT, dut.Y} == exp_sum(dut.A, dut.B, dut.mode))
    else $error("add_sub_4bit mismatch: A=%0h B=%0h mode=%0b -> Y=%0h COUT=%0b (exp=%0h)",
                dut.A, dut.B, dut.mode, dut.Y, dut.COUT, exp_sum(dut.A,dut.B,dut.mode));

  assert property (##0 dut.BOUT == (exp_sum(dut.A, dut.B, dut.mode)[4] ^ dut.mode))
    else $error("add_sub_4bit BOUT mismatch: A=%0h B=%0h mode=%0b -> COUT=%0b BOUT=%0b",
                dut.A, dut.B, dut.mode, dut.COUT, dut.BOUT);

  // Mode-specific relations
  assert property ((dut.mode == 1'b0) |-> ##0 (dut.BOUT == dut.COUT))
    else $error("BOUT should equal COUT in add mode");
  assert property ((dut.mode == 1'b1) |-> ##0 (dut.BOUT == ~dut.COUT))
    else $error("BOUT should be ~COUT in sub mode");

  // X/Z propagation guard: if inputs known, outputs must be known
  assert property ((!$isunknown({dut.A, dut.B, dut.mode})) |-> ##0 (!$isunknown({dut.Y, dut.COUT, dut.BOUT})))
    else $error("Outputs contain X/Z while inputs are known");

  // Focused functional coverage
  cover property (##0 (dut.mode==1'b0 && exp_sum(dut.A, dut.B, 1'b0)[4]==1'b0)); // add, no carry
  cover property (##0 (dut.mode==1'b0 && exp_sum(dut.A, dut.B, 1'b0)[4]==1'b1)); // add, carry
  cover property (##0 (dut.mode==1'b1 && dut.BOUT==1'b0)); // sub, no borrow
  cover property (##0 (dut.mode==1'b1 && dut.BOUT==1'b1)); // sub, borrow
  cover property (##0 (dut.mode==1'b1 && (dut.A==dut.B) && (dut.Y==4'h0) && (dut.BOUT==1'b0))); // A==B

endmodule

bind add_sub_4bit add_sub_4bit_sva i_add_sub_4bit_sva();

`endif