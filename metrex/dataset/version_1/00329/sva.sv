// Bind this checker into your design:
// bind objPixelOn objPixelOn_sva sva_objPixelOn();

module objPixelOn_sva;

  // Expected objSizeOn (mirrors DUT case exactly)
  logic exp_objSizeOn;
  always @* begin
    unique case (objSize)
      3'd0: exp_objSizeOn = ((objByteIndex & 9'b00000001) != 0);
      3'd1: exp_objSizeOn = ((objByteIndex & 9'b00000101) != 0);
      3'd2: exp_objSizeOn = ((objByteIndex & 9'b00010001) != 0);
      3'd3: exp_objSizeOn = ((objByteIndex & 9'b00010101) != 0);
      3'd4: exp_objSizeOn = ((objByteIndex & 9'b10000001) != 0);
      3'd5: exp_objSizeOn = ((objByteIndex & 9'b00000011) != 0);
      3'd6: exp_objSizeOn = ((objByteIndex & 9'b10010001) != 0);
      3'd7: exp_objSizeOn = ((objByteIndex & 9'b00001111) != 0);
    endcase
  end

  // Combinational immediate assertions (no clock required)
  always @* begin
    // Basic signal definitions
    assert (objIndex == pixelNum - objPos - 8'd1)
      else $error("objIndex mismatch");

    assert (objByteIndex == (9'b1 << objIndex[7:3]))
      else $error("objByteIndex mismatch");

    assert (objMaskSel == ((objSize==3'd5) ? objIndex[3:1] :
                           (objSize==3'd7) ? objIndex[4:2] :
                                             objIndex[2:0]))
      else $error("objMaskSel mismatch");

    assert (objMaskOn == objMask[objMaskSel])
      else $error("objMaskOn mismatch");

    assert (objPosOn == ((pixelNum > objPos) &&
                         ({1'b0,pixelNum} <= ({1'b0,objPos} + 9'd72))))
      else $error("objPosOn mismatch");

    assert (objSizeOn == exp_objSizeOn)
      else $error("objSizeOn mismatch");

    assert (pixelOn == (objSizeOn && objMaskOn && objPosOn))
      else $error("pixelOn mismatch");

    // Structural/consistency checks
    assert (!$isunknown(pixelOn)) else $error("pixelOn X/Z");

    if (objPosOn) begin
      assert (objIndex[7:3] <= 4'd8) else $error("objIndex[7:3] out of range when objPosOn");
      assert ($onehot(objByteIndex)) else $error("objByteIndex not onehot when objPosOn");
    end
    assert (objMaskSel <= 3'd7) else $error("objMaskSel out of range");
  end

  // Targeted functional coverage (immediate cover statements)
  always @* begin
    // All sizes hit
    cover (objSize == 3'd0); cover (objSize == 3'd1); cover (objSize == 3'd2); cover (objSize == 3'd3);
    cover (objSize == 3'd4); cover (objSize == 3'd5); cover (objSize == 3'd6); cover (objSize == 3'd7);

    // Position window edge/bounds
    cover (pixelNum == objPos);                             // below window
    cover ({1'b0,pixelNum} == ({1'b0,objPos} + 9'd1));      // first inside
    cover ({1'b0,pixelNum} == ({1'b0,objPos} + 9'd72));     // last inside
    cover ({1'b0,pixelNum} == ({1'b0,objPos} + 9'd73));     // above window
    cover (objPosOn); cover (!objPosOn);

    // Mask select path extremes
    cover (objSize==3'd5 && objIndex[3:1]==3'd0);
    cover (objSize==3'd5 && objIndex[3:1]==3'd7);
    cover (objSize==3'd7 && objIndex[4:2]==3'd0);
    cover (objSize==3'd7 && objIndex[4:2]==3'd7);
    cover ((objSize!=3'd5 && objSize!=3'd7) && objIndex[2:0]==3'd0);
    cover ((objSize!=3'd5 && objSize!=3'd7) && objIndex[2:0]==3'd7);

    // Byte index usage (ensure bit8 is exercised)
    cover (objPosOn && objByteIndex[8]);
    cover (objByteIndex == 9'b0);

    // Gating terms and output toggle
    cover (objMaskOn); cover (!objMaskOn);
    cover (objSizeOn); cover (!objSizeOn);
    cover (pixelOn);   cover (!pixelOn);
  end

endmodule

// Bind directive example:
// bind objPixelOn objPixelOn_sva sva_objPixelOn();