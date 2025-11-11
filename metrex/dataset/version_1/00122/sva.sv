// SVA checker for signed_barrel_shifter
// Bind this module to the DUT instance: 
// bind signed_barrel_shifter signed_barrel_shifter_sva sva(.clk(clk), .rst(rst), .data_in(data_in), .shift_amount(shift_amount), .data_out(data_out), .stage1_out(stage1_out), .stage2_out(stage2_out));

module signed_barrel_shifter_sva(
  input  logic                  clk,
  input  logic                  rst,
  input  logic signed [3:0]     data_in,
  input  logic        [1:0]     shift_amount,
  input  logic signed [3:0]     data_out,
  input  logic signed [3:0]     stage1_out,
  input  logic signed [3:0]     stage2_out
);

  default clocking cb @ (posedge clk); endclocking

  // Local reference functions that mirror DUT coding semantics exactly
  function automatic logic signed [3:0] f_stage1(input logic signed [3:0] di, input logic [1:0] sa);
    f_stage1 = di <<< sa; // left shift (same as << for left)
  endfunction

  function automatic logic signed [3:0] f_stage2(input logic signed [3:0] st1, input logic [1:0] sa);
    // Replicate ternary width behavior: true branch is 2b concatenation zero-extended to 4b
    f_stage2 = sa[1] ? {2'b00, {2{st1[3]}}} : {2'b00, st1[3:2]};
  endfunction

  function automatic logic signed [3:0] f_out(input logic signed [3:0] st2, input logic [1:0] sa);
    // Logical right shift when sa[0]==1 (zero-fill)
    f_out = sa[0] ? (st2 >> 1) : st2;
  endfunction

  // Reset behavior
  assert property (@cb rst |-> (data_out==4'sb0 && stage1_out==4'sb0 && stage2_out==4'sb0))
    else $error("Reset values incorrect");

  // No X/Z on pipeline registers and output after reset deasserted
  assert property (@cb disable iff (rst) !$isunknown({stage1_out, stage2_out, data_out}))
    else $error("Unknown detected on pipeline/output");

  // Pipeline functional checks (1-cycle relations)
  assert property (@cb disable iff (rst) stage1_out == f_stage1($past(data_in), $past(shift_amount)))
    else $error("stage1_out mismatch");
  assert property (@cb disable iff (rst) stage2_out == f_stage2($past(stage1_out), $past(shift_amount)))
    else $error("stage2_out mismatch");
  assert property (@cb disable iff (rst) data_out   == f_out($past(stage2_out), $past(shift_amount)))
    else $error("data_out mismatch");

  // Targeted sign/zero-fill checks implied by DUT code
  // When using >> path, MSB must zero-fill
  assert property (@cb disable iff (rst) $past(shift_amount[0]) |-> (data_out[3]==1'b0))
    else $error("Logical right shift did not zero-fill MSB");
  // When using shift_amount[1] path, upper bits are zero and LSBs replicate sign of prior stage1_out
  assert property (@cb disable iff (rst) $past(shift_amount[1]) |-> (stage2_out[3:2]==2'b00 && stage2_out[1:0]=={2{$past(stage1_out[3])}}))
    else $error("stage2_out format mismatch for shift_amount[1]==1");

  // Minimal, high-value functional coverage
  cover property (@cb rst ##1 !rst); // reset sequence
  cover property (@cb disable iff (rst) (shift_amount==2'b00));
  cover property (@cb disable iff (rst) (shift_amount==2'b01));
  cover property (@cb disable iff (rst) (shift_amount==2'b10));
  cover property (@cb disable iff (rst) (shift_amount==2'b11));
  cover property (@cb disable iff (rst) (data_in[3]==1'b1)); // negative input seen
  cover property (@cb disable iff (rst) ($past(shift_amount[0]) && data_out[3]==1'b0)); // observed zero-fill on >> path

endmodule