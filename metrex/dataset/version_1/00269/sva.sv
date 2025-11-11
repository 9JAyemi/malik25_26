// SVA for SEG7_COUNTER
// Bind this file to the DUT: bind SEG7_COUNTER SEG7_COUNTER_sva u_sva();

module SEG7_COUNTER_sva;
  // Implicitly uses DUT scope (iCLK, iRST, oSEG, count)

  default clocking cb @(posedge iCLK); endclocking

  // Helper for $past safety
  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge iCLK) past_valid <= 1'b1;

  // 7-seg reference decode
  function automatic [6:0] decode7(input logic [3:0] c);
    case (c)
      4'd0: decode7 = 7'b1000000;
      4'd1: decode7 = 7'b1111001;
      4'd2: decode7 = 7'b0100100;
      4'd3: decode7 = 7'b0110000;
      4'd4: decode7 = 7'b0011001;
      4'd5: decode7 = 7'b0010010;
      4'd6: decode7 = 7'b0000010;
      4'd7: decode7 = 7'b1111000;
      4'd8: decode7 = 7'b0000000;
      4'd9: decode7 = 7'b0010000;
      default: decode7 = 7'b1111111;
    endcase
  endfunction

  // No X/Z and legal range
  assert property (!$isunknown(count));
  assert property (count inside {[4'd0:4'd9]});
  assert property (!$isunknown(oSEG));

  // Synchronous reset drives count to 0 next cycle
  assert property (iRST |=> count == 4'd0);

  // Counter sequencing: increment and wrap
  assert property (disable iff (iRST || !past_valid)
                   count < 4'd9 |=> count == $past(count) + 4'd1);
  assert property (disable iff (iRST || !past_valid)
                   count == 4'd9 |=> count == 4'd0);

  // Decode correctness and stability relationship
  assert property (oSEG == decode7(count));
  assert property (disable iff (iRST) $stable(count) |-> $stable(oSEG));

  // Functional coverage
  cover property ($rose(iRST));
  cover property (count == 4'd9 ##1 count == 4'd0);
  generate
    genvar d;
    for (d = 0; d < 10; d++) begin : COV_DIGITS
      cover property (count == d[3:0]);
    end
  endgenerate
endmodule