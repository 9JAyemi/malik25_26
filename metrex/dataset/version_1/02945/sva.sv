// SVA bind module for HEXto7Segment
module HEXto7Segment_sva (
  input logic [3:0] HEXnumber,
  input logic [7:0] Segments
);
  // Golden model for expected 7-seg patterns (active-low)
  function automatic logic [7:0] expected7seg (input logic [3:0] h);
    case (h)
      4'd0:  expected7seg = 8'b1100_0000;
      4'd1:  expected7seg = 8'b1111_1001;
      4'd2:  expected7seg = 8'b1010_0100;
      4'd3:  expected7seg = 8'b1011_0000;
      4'd4:  expected7seg = 8'b1001_1001;
      4'd5:  expected7seg = 8'b1001_0010;
      4'd6:  expected7seg = 8'b1000_0010;
      4'd7:  expected7seg = 8'b1111_1000;
      4'd8:  expected7seg = 8'b1000_0000;
      4'd9:  expected7seg = 8'b1001_0000;
      4'd10: expected7seg = 8'b1000_1000;
      4'd11: expected7seg = 8'b1000_0011;
      4'd12: expected7seg = 8'b1100_0110;
      4'd13: expected7seg = 8'b1010_0001;
      4'd14: expected7seg = 8'b1000_0110;
      4'd15: expected7seg = 8'b1000_1110;
      default: expected7seg = 8'b0000_0000;
    endcase
  endfunction

  // Create a sampling event on any relevant change
  event ev;
  always @(HEXnumber or Segments) -> ev;
  default clocking cb @(ev); endclocking

  // Functional correctness for all known inputs
  assert property ( !$isunknown(HEXnumber) |-> (Segments == expected7seg(HEXnumber)) );

  // Defined behavior for unknown inputs: drives default pattern
  assert property ( $isunknown(HEXnumber) |-> (Segments == 8'b0000_0000) );

  // No X/Z on output when input is known
  assert property ( !$isunknown(HEXnumber) |-> !$isunknown(Segments) );

  // Purely combinational: output stable when input stable (with known inputs)
  assert property ( (!$isunknown(HEXnumber) && !$isunknown($past(HEXnumber))) && $stable(HEXnumber) |-> $stable(Segments) );

  // Zero-latency update on input change (known-to-known)
  assert property ( $changed(HEXnumber) && !$isunknown(HEXnumber) && !$isunknown($past(HEXnumber))
                    |-> ##0 (Segments == expected7seg(HEXnumber)) );

  // Functional coverage: all 16 code points produce the correct pattern
  genvar i;
  generate
    for (i = 0; i < 16; i++) begin : cov_codes
      cover property ( (HEXnumber == i[3:0]) && (Segments == expected7seg(i[3:0])) );
    end
  endgenerate
endmodule

// Bind to DUT
bind HEXto7Segment HEXto7Segment_sva sva (.*);