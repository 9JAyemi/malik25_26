// SVA checker for des_sbox3
// Focus: correctness of mapping, X/Z sanitation, and full input/output coverage.
// Bind this checker to the DUT as shown at the bottom.

`ifndef DES_SBOX3_SVA
`define DES_SBOX3_SVA

module des_sbox3_sva
(
  input logic [0:5] right_xor_key_segment_din,
  input logic [0:3] sbox_dout
);

  // Golden reference function (matches DUT spec)
  function automatic logic [0:3] ref_sbox3(input logic [0:5] din);
    case ({din[0], din[5]})
      2'b00: case (din[1:4])
        4'd0:  ref_sbox3 = 4'd10;
        4'd1:  ref_sbox3 = 4'd0;
        4'd2:  ref_sbox3 = 4'd9;
        4'd3:  ref_sbox3 = 4'd14;
        4'd4:  ref_sbox3 = 4'd6;
        4'd5:  ref_sbox3 = 4'd3;
        4'd6:  ref_sbox3 = 4'd15;
        4'd7:  ref_sbox3 = 4'd5;
        4'd8:  ref_sbox3 = 4'd1;
        4'd9:  ref_sbox3 = 4'd13;
        4'd10: ref_sbox3 = 4'd12;
        4'd11: ref_sbox3 = 4'd7;
        4'd12: ref_sbox3 = 4'd11;
        4'd13: ref_sbox3 = 4'd4;
        4'd14: ref_sbox3 = 4'd2;
        4'd15: ref_sbox3 = 4'd8;
      endcase
      2'b01: case (din[1:4])
        4'd0:  ref_sbox3 = 4'd13;
        4'd1:  ref_sbox3 = 4'd7;
        4'd2:  ref_sbox3 = 4'd0;
        4'd3:  ref_sbox3 = 4'd9;
        4'd4:  ref_sbox3 = 4'd3;
        4'd5:  ref_sbox3 = 4'd4;
        4'd6:  ref_sbox3 = 4'd6;
        4'd7:  ref_sbox3 = 4'd10;
        4'd8:  ref_sbox3 = 4'd2;
        4'd9:  ref_sbox3 = 4'd8;
        4'd10: ref_sbox3 = 4'd5;
        4'd11: ref_sbox3 = 4'd14;
        4'd12: ref_sbox3 = 4'd12;
        4'd13: ref_sbox3 = 4'd11;
        4'd14: ref_sbox3 = 4'd15;
        4'd15: ref_sbox3 = 4'd1;
      endcase
      2'b10: case (din[1:4])
        4'd0:  ref_sbox3 = 4'd13;
        4'd1:  ref_sbox3 = 4'd6;
        4'd2:  ref_sbox3 = 4'd4;
        4'd3:  ref_sbox3 = 4'd9;
        4'd4:  ref_sbox3 = 4'd8;
        4'd5:  ref_sbox3 = 4'd15;
        4'd6:  ref_sbox3 = 4'd3;
        4'd7:  ref_sbox3 = 4'd0;
        4'd8:  ref_sbox3 = 4'd11;
        4'd9:  ref_sbox3 = 4'd1;
        4'd10: ref_sbox3 = 4'd2;
        4'd11: ref_sbox3 = 4'd12;
        4'd12: ref_sbox3 = 4'd5;
        4'd13: ref_sbox3 = 4'd10;
        4'd14: ref_sbox3 = 4'd14;
        4'd15: ref_sbox3 = 4'd7;
      endcase
      2'b11: case (din[1:4])
        4'd0:  ref_sbox3 = 4'd1;
        4'd1:  ref_sbox3 = 4'd10;
        4'd2:  ref_sbox3 = 4'd13;
        4'd3:  ref_sbox3 = 4'd0;
        4'd4:  ref_sbox3 = 4'd6;
        4'd5:  ref_sbox3 = 4'd9;
        4'd6:  ref_sbox3 = 4'd8;
        4'd7:  ref_sbox3 = 4'd7;
        4'd8:  ref_sbox3 = 4'd4;
        4'd9:  ref_sbox3 = 4'd15;
        4'd10: ref_sbox3 = 4'd14;
        4'd11: ref_sbox3 = 4'd3;
        4'd12: ref_sbox3 = 4'd11;
        4'd13: ref_sbox3 = 4'd5;
        4'd14: ref_sbox3 = 4'd2;
        4'd15: ref_sbox3 = 4'd12;
      endcase
    endcase
  endfunction

  // Sanity and functional correctness (immediate assertions)
  always @* begin
    assert (!$isunknown(right_xor_key_segment_din))
      else $error("des_sbox3: X/Z on input right_xor_key_segment_din=%b", right_xor_key_segment_din);

    assert (!$isunknown(sbox_dout))
      else $error("des_sbox3: X/Z on output sbox_dout=%b", sbox_dout);

    if (!$isunknown(right_xor_key_segment_din)) begin
      assert (sbox_dout === ref_sbox3(right_xor_key_segment_din))
        else $error("des_sbox3 mismatch: din=%b got=%0d exp=%0d",
                    right_xor_key_segment_din, sbox_dout, ref_sbox3(right_xor_key_segment_din));
    end
  end

  // Functional coverage: all 64 inputs observed
  genvar i;
  generate
    for (i=0; i<64; i++) begin : cov_in
      localparam logic [5:0] iv = i[5:0];
      localparam logic [0:5] iv_asc = {iv[5],iv[4],iv[3],iv[2],iv[1],iv[0]};
      always @* cover (right_xor_key_segment_din === iv_asc);
    end
  endgenerate

  // Functional coverage: all 16 outputs observed
  genvar j;
  generate
    for (j=0; j<16; j++) begin : cov_out
      localparam logic [3:0] jv = j[3:0];
      localparam logic [0:3] jv_asc = {jv[3],jv[2],jv[1],jv[0]};
      always @* cover (sbox_dout === jv_asc);
    end
  endgenerate

  // Row selection coverage (outer case selector)
  always @* begin
    cover ({right_xor_key_segment_din[0], right_xor_key_segment_din[5]} == 2'b00);
    cover ({right_xor_key_segment_din[0], right_xor_key_segment_din[5]} == 2'b01);
    cover ({right_xor_key_segment_din[0], right_xor_key_segment_din[5]} == 2'b10);
    cover ({right_xor_key_segment_din[0], right_xor_key_segment_din[5]} == 2'b11);
  end

endmodule

// Bind into the DUT (adjust instance name/paths if needed)
bind des_sbox3 des_sbox3_sva sbox3_chk (
  .right_xor_key_segment_din(right_xor_key_segment_din),
  .sbox_dout(sbox_dout)
);

`endif