// SVA checker for seven_seg_decoder
module seven_seg_decoder_sva (
  input  [3:0] num_in,
  input  [1:0] control,
  input        display_sel,
  input  [6:0] seg_out
);

  // Comb event to sample on any input change
  event comb_ev;
  always @* -> comb_ev;
  default clocking cb @(comb_ev); endclocking

  // Helper: override condition
  function automatic bit override_active(input [1:0] c, input bit ds);
    override_active = (c == 2'b11) && (ds == 1'b0);
  endfunction

  // BCD map per DUT
  function automatic [6:0] bcd_map(input [3:0] n);
    case (n)
      4'h0: bcd_map = 7'b1000000;
      4'h1: bcd_map = 7'b1111001;
      4'h2: bcd_map = 7'b0100100;
      4'h3: bcd_map = 7'b0110000;
      4'h4: bcd_map = 7'b0011001;
      4'h5: bcd_map = 7'b0010010;
      4'h6: bcd_map = 7'b0000010;
      4'h7: bcd_map = 7'b1111000;
      4'h8: bcd_map = 7'b0000000;
      4'h9: bcd_map = 7'b0010000;
      4'hA: bcd_map = 7'b1111111;
      4'hB: bcd_map = 7'b1000110;
      default: bcd_map = 7'b0111111;
    endcase
  endfunction

  // HEX map per DUT
  function automatic [6:0] hex_map(input [3:0] n);
    case (n)
      4'h0: hex_map = 7'b1000000;
      4'h1: hex_map = 7'b1111001;
      4'h2: hex_map = 7'b0100100;
      4'h3: hex_map = 7'b0110000;
      4'h4: hex_map = 7'b0011001;
      4'h5: hex_map = 7'b0010010;
      4'h6: hex_map = 7'b0000010;
      4'h7: hex_map = 7'b1111000;
      4'h8: hex_map = 7'b0000000;
      4'h9: hex_map = 7'b0010000;
      4'hA: hex_map = 7'b0001000;
      4'hB: hex_map = 7'b0000011;
      4'hC: hex_map = 7'b1000110;
      4'hD: hex_map = 7'b0100001;
      4'hE: hex_map = 7'b0000110;
      default: hex_map = 7'b0001110; // 4'hF
    endcase
  endfunction

  // Expected output per DUT spec (override > select)
  function automatic [6:0] expected_seg(
    input [3:0] n, input [1:0] c, input bit ds
  );
    if (override_active(c, ds)) expected_seg = 7'b0001001;
    else expected_seg = ds ? bcd_map(n) : hex_map(n);
  endfunction

  // Core functional check (covers all cases concisely)
  assert property ( seg_out == expected_seg(num_in, control, display_sel) )
    else $error("seven_seg_decoder mismatch: n=%0h c=%0b ds=%0b seg=%0b exp=%0b",
                num_in, control, display_sel, seg_out, expected_seg(num_in,control,display_sel));

  // Override value check (redundant but explicit)
  assert property ( override_active(control, display_sel) |-> seg_out == 7'b0001001 )
    else $error("Override active but seg_out != 7'b0001001");

  // Select-path checks (redundant slice of core check; helps localize)
  assert property ( !override_active(control,display_sel) && display_sel
                    |-> seg_out == bcd_map(num_in) );
  assert property ( !override_active(control,display_sel) && !display_sel
                    |-> seg_out == hex_map(num_in) );

  // For 0..9, BCD and HEX maps must match (sanity of tables)
  assert property ( !override_active(control,display_sel) && (num_in <= 4'd9)
                    |-> (bcd_map(num_in) == hex_map(num_in)) );

  // No X/Z on output when inputs are known
  assert property ( !$isunknown({num_in, control, display_sel}) |-> !$isunknown(seg_out) );

  // --------- Coverage ---------
  // Override hit
  cover property ( override_active(control, display_sel) );

  // Both display selections
  cover property ( !display_sel );
  cover property (  display_sel );

  // All control values
  genvar ci;
  generate
    for (ci = 0; ci < 4; ci++) begin : C_CTRL
      cover property ( control == ci[1:0] );
    end
  endgenerate

  // All num_in values observed on each path (when not overridden)
  genvar ni;
  generate
    for (ni = 0; ni < 16; ni++) begin : C_NUM
      cover property ( !override_active(control,display_sel) &&  display_sel && (num_in == ni[3:0]) );
      cover property ( !override_active(control,display_sel) && !display_sel && (num_in == ni[3:0]) );
    end
  endgenerate

endmodule

// Bind into DUT
bind seven_seg_decoder seven_seg_decoder_sva seven_seg_decoder_sva_b(.num_in(num_in),
                                                                     .control(control),
                                                                     .display_sel(display_sel),
                                                                     .seg_out(seg_out));