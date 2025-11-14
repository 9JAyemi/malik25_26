// SVA for gci_std_display_font
// Bind example (in your TB or a separate file):
// bind gci_std_display_font gci_std_display_font_sva sva_inst(.iADDR(iADDR), .oDATA(oDATA));

module gci_std_display_font_sva(
  input  logic [6:0]   iADDR,
  input  logic [111:0] oDATA
);

  // Golden model of the ROM (bit-for-bit copy of DUT contents)
  function automatic [111:0] golden_rom(input [6:0] funcADDR);
    begin
      case (funcADDR)
        7'd0:  golden_rom = 112'h0000000000000000000000000000;
        7'd1:  golden_rom = 112'h0000181818181010100000181800;
        7'd2:  golden_rom = 112'h006c6c2448000000000000000000;
        7'd3:  golden_rom = 112'h00002424247e2424487e48484800;
        7'd4:  golden_rom = 112'h0000103c525250381452523c1000;
        7'd5:  golden_rom = 112'h0000225254542818142a2a4A4400;
        7'd6:  golden_rom = 112'h0000102828102652524c442a1000;
        7'd7:  golden_rom = 112'h0030301020000000000000000000;
        7'd8:  golden_rom = 112'h0004081010202020202010100804;
        7'd9:  golden_rom = 112'h0020100808040404040408081020;
        7'd10: golden_rom = 112'h0000001010d6543854d610100000;
        7'd11: golden_rom = 112'h000000101010107e101010100000;
        7'd12: golden_rom = 112'h0000000000000000000030301020;
        7'd13: golden_rom = 112'h000000000000007e000000000000;
        7'd14: golden_rom = 112'h0000000000000000000000303000;
        7'd15: golden_rom = 112'h0202040408081010202040408080;
        7'd16: golden_rom = 112'h0000182424424242411224180000;
        7'd17: golden_rom = 112'h00001070101010101010107c0000;
        7'd18: golden_rom = 112'h00001824422204081020227e0000;
        7'd19: golden_rom = 112'h0000182442441804424112180000;
        7'd20: golden_rom = 112'h0000040C141424247e04040e0000;
        7'd21: golden_rom = 112'h00007c4040586442024112180000;
        7'd22: golden_rom = 112'h00001c1122586442424112180000;
        7'd23: golden_rom = 112'h00003e1122040408080808080000;
        7'd24: golden_rom = 112'h0000182441121824424112180000;
        7'd25: golden_rom = 112'h000018244242261a024424180000;
        7'd26: golden_rom = 112'h0000000018180000001818000000;
        7'd27: golden_rom = 112'h0000000018180000001818081000;
        7'd28: golden_rom = 112'h0000020408102040201008040200;
        7'd29: golden_rom = 112'h000000007e0000007E0000000000;
        7'd30: golden_rom = 112'h0000402010080402040810204000;
        7'd31: golden_rom = 112'h0000182442420408101000181800;
        7'd32: golden_rom = 112'h00001824112A5656564A20221C00;
        7'd33: golden_rom = 112'h00001010282828247c4444ee0000;
        7'd34: golden_rom = 112'h0000782424283c22222112780000;
        7'd35: golden_rom = 112'h00001a2611224040402226180000;
        7'd36: golden_rom = 112'h0000782424222222211224780000;
        7'd37: golden_rom = 112'h00007c2220243c242020227e0000;
        7'd38: golden_rom = 112'h00007c2220243c24202020780000;
        7'd39: golden_rom = 112'h00001a261122404e4222261a0000;
        7'd40: golden_rom = 112'h0000ee4444447c44444444ee0000;
        7'd41: golden_rom = 112'h00007c10101010101010107c0000;
        7'd42: golden_rom = 112'h00001e0404040404444448300000;
        7'd43: golden_rom = 112'h00006e2428283028242422760000;
        7'd44: golden_rom = 112'h00007020202020202020227c0000;
        7'd45: golden_rom = 112'h00004266666a5a52524242660000;
        7'd46: golden_rom = 112'h000046626252524A4a4646620000;
        7'd47: golden_rom = 112'h0000182442424242424112180000;
        7'd48: golden_rom = 112'h0000782422211238202020700000;
        7'd49: golden_rom = 112'h0000182442424242724e24180600;
        7'd50: golden_rom = 112'h0000782422211238282424720000;
        7'd51: golden_rom = 112'h00001a2642201804024264580000;
        7'd52: golden_rom = 112'h00007e5210101010101010380000;
        7'd53: golden_rom = 112'h0000762222222222222214080000;
        7'd54: golden_rom = 112'h0000664112242428181010100000;
        7'd55: golden_rom = 112'h0000929292525A6A6c2424240000;
        7'd56: golden_rom = 112'h00006244242810182824444e0000;
        7'd57: golden_rom = 112'h0000e64112281810101010380000;
        7'd58: golden_rom = 112'h00003e44040808102020427c0000;
        7'd59: golden_rom = 112'h003c20202020202020202020203C;
        7'd60: golden_rom = 112'h8080404020201010080804040202;
        7'd61: golden_rom = 112'h003c04040404040404040404043C;
        7'd62: golden_rom = 112'h0010284482000000000000000000;
        7'd63: golden_rom = 112'h00000000000000000000000000FE;
        7'd64: golden_rom = 112'h0018181008000000000000000000;
        7'd65: golden_rom = 112'h000000003844441c2444443a0000;
        7'd66: golden_rom = 112'h0000602028342222222112380000;
        7'd67: golden_rom = 112'h000000001a264240404226180000;
        7'd68: golden_rom = 112'h00000c04142c44444444241e0000;
        7'd69: golden_rom = 112'h000000001824427e4042221c0000;
        7'd70: golden_rom = 112'h00000c12127c1010101010380000;
        7'd71: golden_rom = 112'h000000001a24242418205c42423C;
        7'd72: golden_rom = 112'h0000c04050684444444444c60000;
        7'd73: golden_rom = 112'h00001818003808080808083c0000;
        7'd74: golden_rom = 112'h00000c0c001c0404040404444830;
        7'd75: golden_rom = 112'h0000c04046444858684444ce0000;
        7'd76: golden_rom = 112'h00003808080808080808083e0000;
        7'd77: golden_rom = 112'h00000000acd29292929292920000;
        7'd78: golden_rom = 112'h00000000d8644444444444c60000;
        7'd79: golden_rom = 112'h0000000018244242424112180000;
        7'd80: golden_rom = 112'h0000000058242222222112382070;
        7'd81: golden_rom = 112'h000000001a2444444444241c040E;
        7'd82: golden_rom = 112'h000000005c222220202020700000;
        7'd83: golden_rom = 112'h000000003c4440300c42625c0000;
        7'd84: golden_rom = 112'h00001010107c10101010120c0000;
        7'd85: golden_rom = 112'h00000000cc44444444444c320000;
        7'd86: golden_rom = 112'h0000000066424424281810100000;
        7'd87: golden_rom = 112'h00000000929292925A6c24240000;
        7'd88: golden_rom = 112'h0000000066242818181424660000;
        7'd89: golden_rom = 112'h0000000066222214140808485020;
        7'd90: golden_rom = 112'h000000003e4408081010227e0000;
        7'd91: golden_rom = 112'h0006081010101020101010100806;
        7'd92: golden_rom = 112'h0010101010101010101010101010;
        7'd93: golden_rom = 112'h0060100808080804080808081060;
        default: golden_rom = 112'h0000000000000000000000000000;
      endcase
    end
  endfunction

  // Core correctness: output must equal golden ROM at the translated address
  always_comb begin
    assert (oDATA == golden_rom(iADDR - 8'h20))
      else $error("gci_std_display_font: oDATA mismatch for iADDR=0x%0h (idx=0x%0h)", iADDR, (iADDR - 8'h20));

    // No X/Z on interface
    assert (!$isunknown(iADDR)) else $error("gci_std_display_font: iADDR has X/Z");
    assert (!$isunknown(oDATA)) else $error("gci_std_display_font: oDATA has X/Z");

    // Out-of-range addresses must map to all zeros via default
    if (iADDR < 7'h20 || iADDR > 7'h7D) begin
      assert (oDATA == '0)
        else $error("gci_std_display_font: out-of-range iADDR=0x%0h should yield zero", iADDR);
    end else begin
      // Sanity: space (0x20) is all-zero; all other valid glyphs are non-zero
      if (iADDR == 7'h20) begin
        assert (oDATA == '0)
          else $error("gci_std_display_font: space glyph (0x20) must be zero");
      end else begin
        assert (oDATA != '0)
          else $error("gci_std_display_font: non-space valid glyph at iADDR=0x%0h is unexpectedly zero", iADDR);
      end
    end
  end

  // Functional coverage: hit every valid code point and both invalid regions
  covergroup cg_addr;
    coverpoint iADDR {
      bins valid[]     = {[7'h20:7'h7D]};  // one bin per valid address (full coverage of ROM rows)
      bins invalid_lo  = {[7'h00:7'h1F]};
      bins invalid_hi  = {[7'h7E:7'h7F]};
    }
    coverpoint (oDATA == 112'h0) { bins zero = {1}; bins nonzero = {0}; }
    cross iADDR, (oDATA == 112'h0);
  endgroup
  cg_addr cg = new();

  // Sample coverage when address changes (concise, clockless)
  always @(iADDR) cg.sample();

endmodule