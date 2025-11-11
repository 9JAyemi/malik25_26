// SVA for binary_to_bcd. Bind to the DUT and drive clk from TB.
// These assertions define the correct, concise golden behavior and key checks.

module binary_to_bcd_sva (
  input logic        clk,
  input logic [3:0]  binary_in,
  input logic [15:0] bcd_out
);

  // Golden model: BCD = {8'h00, tens, ones}, tens=(bin>=10), ones=bin-10*tens
  function automatic [15:0] golden_bcd(input logic [3:0] bin);
    automatic int d = bin;
    automatic logic [3:0] tens = (d >= 10) ? 4'd1 : 4'd0;
    automatic logic [3:0] ones = d - (tens*10);
    golden_bcd = {8'h00, tens, ones};
  endfunction

  function automatic int bcd_to_int(input logic [15:0] b);
    return 10*int'(b[7:4]) + int'(b[3:0]);
  endfunction

  default clocking cb @(posedge clk); endclocking

  // No X on output when input is known
  assert property (!$isunknown(binary_in) |-> !$isunknown(bcd_out))
    else $error("binary_to_bcd: X-prop: known input produced unknown output");

  // Output must exactly equal golden BCD encoding
  assert property (1'b1 |-> ##0 (bcd_out === golden_bcd(binary_in)))
    else $error("binary_to_bcd: output does not match golden BCD");

  // Structural BCD sanity
  assert property (1'b1 |-> ##0 (bcd_out[15:8] == 8'h00))
    else $error("binary_to_bcd: upper bytes not zero");
  assert property (1'b1 |-> ##0 (bcd_out[7:4] <= 4'd9 && bcd_out[3:0] <= 4'd9))
    else $error("binary_to_bcd: invalid BCD digit");

  // Range-specific constraints for 4-bit input domain
  assert property ((binary_in <= 4'd9)  |-> ##0 (bcd_out[7:4] == 4'd0 && bcd_out[3:0] == binary_in))
    else $error("binary_to_bcd: 0..9 mapping wrong");
  assert property ((binary_in >= 4'd10) |-> ##0 (bcd_out[7:4] == 4'd1 && bcd_out[3:0] == (binary_in-4'd10)))
    else $error("binary_to_bcd: 10..15 mapping wrong");

  // Monotonicity on +1 steps (no wrap)
  assert property (($past(binary_in) < 4'd15 && binary_in == $past(binary_in)+1)
                   |-> bcd_to_int(bcd_out) == bcd_to_int(golden_bcd($past(binary_in))) + 1)
    else $error("binary_to_bcd: +1 step did not increment BCD by 1");

  // Key coverage
  cover property (binary_in == 4'd0);
  cover property (binary_in == 4'd9);
  cover property (binary_in == 4'd10);
  cover property (binary_in == 4'd15);
  cover property ($past(binary_in)==4'd9 && binary_in==4'd10); // 9->10 carry to tens

endmodule

// Example bind (adjust clk name as appropriate in your environment):
// bind binary_to_bcd binary_to_bcd_sva sva_inst(.* , .clk(tb_clk));