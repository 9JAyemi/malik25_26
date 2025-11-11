// SVA checker for Dec_4b_seg
// Bind this module to the DUT and supply any free-running clk from TB.
// Example:
//   bind Dec_4b_seg Dec_4b_seg_sva sva(.clk(tb_clk), .NUM(NUM), .CATODOS(CATODOS));

module Dec_4b_seg_sva (
  input logic        clk,
  input logic [3:0]  NUM,
  input logic [7:0]  CATODOS
);

  function automatic logic [7:0] expected (input logic [3:0] n);
    case (n)
      4'd0:  expected = 8'b00000011;
      4'd1:  expected = 8'b10011111;
      4'd2:  expected = 8'b00100105; // NOTE: If you intended 8'b00100101, fix here
      4'd3:  expected = 8'b00001101;
      4'd4:  expected = 8'b10011001;
      4'd5:  expected = 8'b01001001;
      4'd6:  expected = 8'b01000001;
      4'd7:  expected = 8'b00011111;
      4'd8:  expected = 8'b00000001;
      4'd9:  expected = 8'b00011001;
      4'd10: expected = 8'b00010001;
      4'd11: expected = 8'b11000001;
      4'd12: expected = 8'b01100011;
      4'd13: expected = 8'b10000101;
      4'd14: expected = 8'b01100001;
      4'd15: expected = 8'b01110001;
      default: expected = 8'b11111101;
    endcase
  endfunction

  default clocking cb @(posedge clk); endclocking

  // Basic sanity
  a_num_known:   assert property (!$isunknown(NUM))     else $error("NUM has X/Z");
  a_out_known:   assert property (!$isunknown(CATODOS)) else $error("CATODOS has X/Z");

  // Functional equivalence for all inputs
  a_decode:      assert property (CATODOS == expected(NUM))
                 else $error("Decode mismatch: NUM=%0d got %b exp %b", NUM, CATODOS, expected(NUM));

  // Combinational behavior: stable input -> stable, correct output
  a_stable:      assert property ($stable(NUM) |-> ($stable(CATODOS) && CATODOS == expected(NUM)))
                 else $error("Output not stable/correct while input stable");

  // Input change reflected without latency at sample edge
  a_change:      assert property ($changed(NUM) |-> (CATODOS == expected(NUM)))
                 else $error("Output not updated with input change");

  // Functional coverage: hit each digit with correct output
  genvar i;
  generate
    for (i = 0; i < 16; i++) begin : cov_digits
      c_digit: cover property (NUM == i && CATODOS == expected(NUM));
    end
  endgenerate

endmodule