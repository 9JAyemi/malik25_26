// SVA for bcd_converter: checks correctness, structure, X-prop, and provides concise coverage.
module bcd_converter_sva (
  input logic [3:0]  input_val,
  input logic [15:0] bcd_val
);

  function automatic logic [15:0] exp_bcd (input logic [3:0] v);
    case (v)
      4'd0: exp_bcd = 16'h0000;
      4'd1: exp_bcd = 16'h0001;
      4'd2: exp_bcd = 16'h0002;
      4'd3: exp_bcd = 16'h0003;
      4'd4: exp_bcd = 16'h0004;
      4'd5: exp_bcd = 16'h0005;
      4'd6: exp_bcd = 16'h0006;
      4'd7: exp_bcd = 16'h0007;
      4'd8: exp_bcd = 16'h0008;
      4'd9: exp_bcd = 16'h0009;
      default: exp_bcd = 16'h0000;
    endcase
  endfunction

  // Sample on any edge of input_val bits (combinational change)
  `define COMB_EV (posedge input_val[0] or negedge input_val[0] or \
                    posedge input_val[1] or negedge input_val[1] or \
                    posedge input_val[2] or negedge input_val[2] or \
                    posedge input_val[3] or negedge input_val[3])

  // Correct mapping at the same time of input change
  property p_map;
    @(`COMB_EV) 1 |-> (bcd_val === exp_bcd(input_val));
  endproperty
  a_map: assert property (p_map) else $error("bcd_val mismatch: in=%0d got=%h exp=%h", input_val, bcd_val, exp_bcd(input_val));

  // Structural BCD form for 0..9: upper 12 bits zero and low nibble equals input
  property p_struct_legal;
    @(`COMB_EV) (input_val <= 4'd9) |-> (bcd_val[15:4] == 12'h000 && bcd_val[3:0] == input_val);
  endproperty
  a_struct_legal: assert property (p_struct_legal) else $error("Illegal BCD structure for legal input %0d: %h", input_val, bcd_val);

  // Illegal inputs (10..15) map to zero
  property p_illegal_zero;
    @(`COMB_EV) (input_val >= 4'd10) |-> (bcd_val == 16'h0000);
  endproperty
  a_illegal_zero: assert property (p_illegal_zero) else $error("Illegal input %0d should map to 0, got %h", input_val, bcd_val);

  // No X/Z on output when input is known
  property p_no_x;
    @(`COMB_EV) (!$isunknown(input_val)) |-> (!$isunknown(bcd_val));
  endproperty
  a_no_x: assert property (p_no_x) else $error("X/Z detected on bcd_val for known input %0d: %h", input_val, bcd_val);

  // Coverage: each legal digit observed with correct output
  genvar d;
  generate
    for (d = 0; d <= 9; d++) begin : cov_digits
      cover property (@(`COMB_EV) input_val == d[3:0] && bcd_val == exp_bcd(d[3:0]));
    end
  endgenerate

  // Coverage: at least one illegal input seen and mapped to zero
  cover property (@(`COMB_EV) input_val inside {[4'hA:4'hF]} && bcd_val == 16'h0000);

  `undef COMB_EV

endmodule

// Bind into the DUT
bind bcd_converter bcd_converter_sva u_bcd_converter_sva(.input_val(input_val), .bcd_val(bcd_val));