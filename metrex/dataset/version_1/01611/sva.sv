// SVA checker for des_sbox8. Bind this to the DUT.
module des_sbox8_sva
(
  input wire [0:5] right_xor_key_segment_din,
  input wire [0:3] sbox_dout
);

  // Reference S8 table (row = {bit0,bit5}, col = bits[1:4])
  localparam logic [3:0] S8 [0:3][0:15] = '{
    0: '{13,2,8,4,6,15,11,1,10,9,3,14,5,0,12,7},
    1: '{1,15,13,8,10,3,7,4,12,5,6,11,0,14,9,2},
    2: '{7,11,4,1,9,12,14,2,0,6,10,13,15,3,5,8},
    3: '{2,1,14,7,4,10,8,13,15,12,9,0,3,5,6,11}
  };

  logic [1:0] row;
  logic [3:0] col;
  logic [3:0] expected;

  always_comb begin
    row = {right_xor_key_segment_din[0], right_xor_key_segment_din[5]};
    col = right_xor_key_segment_din[1:4];
    expected = S8[row][col];

    // No X/Z on inputs/outputs
    assert (!$isunknown(right_xor_key_segment_din))
      else $error("des_sbox8: X/Z on input: %b", right_xor_key_segment_din);
    if (!$isunknown(right_xor_key_segment_din)) begin
      assert (!$isunknown(sbox_dout))
        else $error("des_sbox8: X/Z on output for row=%0d col=%0d", row, col);

      // Functional equivalence to reference table
      assert (sbox_dout == expected)
        else $error("des_sbox8 mismatch: row=%0d col=%0d exp=%0d got=%0d",
                    row, col, expected, sbox_dout);
    end
  end

  // Functional coverage: all 64 addressable entries + all outputs
  covergroup cg_sbox @(right_xor_key_segment_din);
    cp_row: coverpoint row { bins rows[] = {[0:3]}; }
    cp_col: coverpoint col { bins cols[] = {[0:15]}; }
    x_row_col: cross cp_row, cp_col;
    cp_out: coverpoint sbox_dout { bins vals[] = {[0:15]}; }
  endgroup
  cg_sbox cg = new();

endmodule

bind des_sbox8 des_sbox8_sva u_des_sbox8_sva (.*);