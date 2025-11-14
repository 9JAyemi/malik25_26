// SVA for DecodeUnit (combinational decode checks + focused coverage)
// Bind this module to the DUT:  bind DecodeUnit DecodeUnit_sva dut_sva();

module DecodeUnit_sva (DecodeUnit dut);

  // ALU opcodes (mirrors DUT)
  localparam logic [3:0] IADD=4'b0000, ISUB=4'b0001, IAND=4'b0010, IOR=4'b0011, IXOR=4'b0100;
  localparam logic [3:0] ISLL=4'b1000, ISLR=4'b1001, ISRL=4'b1010, ISRA=4'b1011, IIDT=4'b1100, INON=4'b1111;

  function automatic logic [3:0] exp_S_ALU (logic [15:0] C);
    if (C[15:14]==2'b11) begin
      case (C[7:4])
        4'b0101: return ISUB;
        4'b0110: return IIDT;
        default: return C[7:4];
      endcase
    end
    else if (C[15]==1'b0)                    return IADD;
    else if (C[15:11]==5'b10000)             return IIDT;
    else if (C[15:11]==5'b10001)             return IADD;
    else if (C[15:11]==5'b10101 || C[15:11]==5'b10110) return ISUB;
    else if (C[15:11]==5'b10100)             return IADD;
    else if (C[15:11]==5'b10111)             return IADD;
    else if (C[15:11]==5'b10011)             return IADD;
    else                                     return INON;
  endfunction

  function automatic logic exp_FLAG_WRITE (logic [15:0] C);
    return ((C[15:14]==2'b11 && (C[7:4] >= 4'b0000 && C[7:4] <= 4'b1011) && C[7:4] != 4'b0111)
            || (C[15:11]==5'b10001));
  endfunction

  always_comb begin
    // No-X on outputs
    assert (!$isunknown({dut.out, dut.INPUT_MUX, dut.writeEnable, dut.writeAddress,
                         dut.ADR_MUX, dut.write, dut.PC_load, dut.SP_write, dut.inc, dut.dec,
                         dut.cond, dut.op2, dut.SP_Sw, dut.MAD_MUX, dut.FLAG_WRITE,
                         dut.AR_MUX, dut.BR_MUX, dut.S_ALU, dut.SPC_MUX, dut.MW_MUX,
                         dut.AB_MUX, dut.signEx}))
      else $error("DecodeUnit outputs contain X/Z for COMMAND=%h", dut.COMMAND);

    // Exact decode checks (assert functional equivalence)
    assert (dut.FLAG_WRITE == exp_FLAG_WRITE(dut.COMMAND))
      else $error("FLAG_WRITE mismatch CMD=%h", dut.COMMAND);

    assert (dut.SPC_MUX == ((dut.COMMAND[15:11]==5'b10011) || (dut.COMMAND[15:11]==5'b10101)))
      else $error("SPC_MUX mismatch CMD=%h", dut.COMMAND);

    assert (dut.AB_MUX == (dut.COMMAND[15:14]==2'b01))
      else $error("AB_MUX mismatch CMD=%h", dut.COMMAND);

    assert (dut.MW_MUX == (dut.COMMAND[15:8] != 8'b10111110))
      else $error("MW_MUX mismatch CMD=%h", dut.COMMAND);

    assert (dut.SP_Sw == (dut.COMMAND[15:8] != 8'b10111111))
      else $error("SP_Sw mismatch CMD=%h", dut.COMMAND);

    assert (dut.MAD_MUX == ~((dut.COMMAND[15:11]==5'b10010) || (dut.COMMAND[15:9]==7'b1011111)))
      else $error("MAD_MUX mismatch CMD=%h", dut.COMMAND);

    assert (dut.inc == ((dut.COMMAND[15:8]==8'b10111110) || (dut.COMMAND[15:11]==5'b10010)))
      else $error("inc mismatch CMD=%h", dut.COMMAND);

    assert (dut.dec == ((dut.COMMAND[15:8]==8'b10111111) || (dut.COMMAND[15:11]==5'b10011)))
      else $error("dec mismatch CMD=%h", dut.COMMAND);

    assert (dut.SP_write == (dut.COMMAND[15:11]==5'b10011))
      else $error("SP_write mismatch CMD=%h", dut.COMMAND);

    assert (dut.writeAddress == ((dut.COMMAND[15:14]==2'b00) ? dut.COMMAND[13:11] : dut.COMMAND[10:8]))
      else $error("writeAddress mismatch CMD=%h", dut.COMMAND);

    assert (dut.cond == dut.COMMAND[10:8])
      else $error("cond mismatch CMD=%h", dut.COMMAND);

    assert (dut.op2 == dut.COMMAND[13:11])
      else $error("op2 mismatch CMD=%h", dut.COMMAND);

    assert (dut.writeEnable == ((dut.COMMAND[15:14]==2'b01)
                                || (dut.COMMAND[15:11]==5'b10010)
                                || (dut.COMMAND[15:11]==5'b10110)
                                || (dut.COMMAND[15:8]==8'b10111110)))
      else $error("writeEnable mismatch CMD=%h", dut.COMMAND);

    assert (dut.signEx == (dut.COMMAND[15:14] != 2'b11))
      else $error("signEx mismatch CMD=%h", dut.COMMAND);

    assert (dut.out == (dut.COMMAND[15:14]==2'b11 && dut.COMMAND[7:4]==4'b1101))
      else $error("out mismatch CMD=%h", dut.COMMAND);

    assert (dut.write == (((dut.COMMAND[15:14]==2'b11) && (dut.COMMAND[7:4] <= 4'b1100) && (dut.COMMAND[7:4] != 4'b0101))
                          || (dut.COMMAND[15:14]==2'b00)
                          || (dut.COMMAND[15:12]==4'b1000)
                          || (dut.COMMAND[15:11]==5'b10011)
                          || (dut.COMMAND[15:11]==5'b10101)))
      else $error("write mismatch CMD=%h", dut.COMMAND);

    assert (dut.PC_load == ((dut.COMMAND[15:11]==5'b10100) || (dut.COMMAND[15:11]==5'b10111)))
      else $error("PC_load mismatch CMD=%h", dut.COMMAND);

    assert (dut.INPUT_MUX == (dut.COMMAND[15:14]==2'b11 && dut.COMMAND[7:4]==4'b1100))
      else $error("INPUT_MUX mismatch CMD=%h", dut.COMMAND);

    assert (dut.ADR_MUX == (((dut.COMMAND[15:14]==2'b11) && (dut.COMMAND[7:4] <= 4'b1011))
                            || ((dut.COMMAND[15:14]==2'b10) && (dut.COMMAND[13:11] <= 3'b100) && (dut.COMMAND[13:11] != 3'b011))
                            || ((dut.COMMAND[15:11]==5'b10111) && (dut.COMMAND[10:8] != 3'b111))))
      else $error("ADR_MUX mismatch CMD=%h", dut.COMMAND);

    assert (dut.BR_MUX == ((dut.COMMAND[15:14]==2'b11) || (dut.COMMAND[15:11]==5'b10001) || (dut.COMMAND[15:14]==2'b01) || (dut.COMMAND[15:14]==2'b00)))
      else $error("BR_MUX mismatch CMD=%h", dut.COMMAND);

    assert (dut.AR_MUX == (dut.COMMAND[15:14]==2'b11 && dut.COMMAND[7:4] <= 4'b0110))
      else $error("AR_MUX mismatch CMD=%h", dut.COMMAND);

    assert (dut.S_ALU == exp_S_ALU(dut.COMMAND))
      else $error("S_ALU mismatch CMD=%h exp=%b got=%b", dut.COMMAND, exp_S_ALU(dut.COMMAND), dut.S_ALU);

    // Focused coverage (hit all key decode reasons and opcodes)
    cover (dut.FLAG_WRITE && dut.COMMAND[15:14]==2'b11 && dut.COMMAND[7:4] inside {[4'b0000:4'b1011]} && dut.COMMAND[7:4]!=4'b0111);
    cover (dut.FLAG_WRITE && dut.COMMAND[15:11]==5'b10001);

    cover (dut.SPC_MUX && dut.COMMAND[15:11]==5'b10011);
    cover (dut.SPC_MUX && dut.COMMAND[15:11]==5'b10101);

    cover (dut.AB_MUX && dut.COMMAND[15:14]==2'b01);
    cover (!dut.AB_MUX && dut.COMMAND[15:14]!=2'b01);

    cover (!dut.MW_MUX && dut.COMMAND[15:8]==8'b10111110);
    cover (!dut.SP_Sw && dut.COMMAND[15:8]==8'b10111111);
    cover (!dut.MAD_MUX && (dut.COMMAND[15:11]==5'b10010));
    cover (!dut.MAD_MUX && (dut.COMMAND[15:9]==7'b1011111));

    cover (dut.inc && (dut.COMMAND[15:8]==8'b10111110));
    cover (dut.inc && (dut.COMMAND[15:11]==5'b10010));
    cover (dut.dec && (dut.COMMAND[15:8]==8'b10111111));
    cover (dut.dec && (dut.COMMAND[15:11]==5'b10011));
    cover (dut.SP_write && dut.COMMAND[15:11]==5'b10011);

    cover (dut.writeAddress == dut.COMMAND[13:11] && dut.COMMAND[15:14]==2'b00);
    cover (dut.writeAddress == dut.COMMAND[10:8]  && dut.COMMAND[15:14]!=2'b00);

    cover (dut.signEx && dut.COMMAND[15:14]!=2'b11);
    cover (!dut.signEx && dut.COMMAND[15:14]==2'b11);

    cover (dut.out && dut.COMMAND[15:14]==2'b11 && dut.COMMAND[7:4]==4'b1101);
    cover (dut.INPUT_MUX && dut.COMMAND[15:14]==2'b11 && dut.COMMAND[7:4]==4'b1100);

    cover (dut.ADR_MUX && dut.COMMAND[15:14]==2'b11 && dut.COMMAND[7:4] <= 4'b1011);
    cover (dut.ADR_MUX && dut.COMMAND[15:14]==2'b10 && dut.COMMAND[13:11] <= 3'b100 && dut.COMMAND[13:11] != 3'b011);
    cover (dut.ADR_MUX && dut.COMMAND[15:11]==5'b10111 && dut.COMMAND[10:8] != 3'b111);

    cover (dut.BR_MUX && dut.COMMAND[15:14]==2'b11);
    cover (dut.BR_MUX && dut.COMMAND[15:11]==5'b10001);
    cover (!dut.BR_MUX && dut.COMMAND[15:14]==2'b10 && dut.COMMAND[15:11]!=5'b10001);

    cover (dut.AR_MUX && dut.COMMAND[15:14]==2'b11 && dut.COMMAND[7:4]==4'b0000);
    cover (dut.AR_MUX && dut.COMMAND[15:14]==2'b11 && dut.COMMAND[7:4]==4'b0110);
    cover (!dut.AR_MUX && (dut.COMMAND[15:14]!=2'b11 || dut.COMMAND[7:4]>4'b0110));

    cover (dut.PC_load && dut.COMMAND[15:11]==5'b10100);
    cover (dut.PC_load && dut.COMMAND[15:11]==5'b10111);

    // ALU opcode coverage (key ops and special remaps)
    cover (dut.S_ALU==IADD && dut.COMMAND[15]==1'b0);
    cover (dut.S_ALU==ISUB && dut.COMMAND[15:14]==2'b11 && dut.COMMAND[7:4]==4'b0101);
    cover (dut.S_ALU==IIDT && dut.COMMAND[15:14]==2'b11 && dut.COMMAND[7:4]==4'b0110);
    cover (dut.S_ALU==IIDT && dut.COMMAND[15:11]==5'b10000);
    cover (dut.S_ALU==ISUB && (dut.COMMAND[15:11] inside {5'b10101,5'b10110}));
    cover (dut.S_ALU==ISLL && dut.COMMAND[15:14]==2'b11 && dut.COMMAND[7:4]==4'b1000);
    cover (dut.S_ALU==ISLR && dut.COMMAND[15:14]==2'b11 && dut.COMMAND[7:4]==4'b1001);
    cover (dut.S_ALU==ISRL && dut.COMMAND[15:14]==2'b11 && dut.COMMAND[7:4]==4'b1010);
    cover (dut.S_ALU==ISRA && dut.COMMAND[15:14]==2'b11 && dut.COMMAND[7:4]==4'b1011);
    cover (dut.S_ALU==IAND && dut.COMMAND[15:14]==2'b11 && dut.COMMAND[7:4]==4'b0010);
    cover (dut.S_ALU==IOR  && dut.COMMAND[15:14]==2'b11 && dut.COMMAND[7:4]==4'b0011);
    cover (dut.S_ALU==IXOR && dut.COMMAND[15:14]==2'b11 && dut.COMMAND[7:4]==4'b0100);
    cover (dut.S_ALU==INON);

    // Write signal reasons
    cover (dut.write && dut.COMMAND[15:14]==2'b11 && dut.COMMAND[7:4] <= 4'b1100 && dut.COMMAND[7:4] != 4'b0101);
    cover (dut.write && dut.COMMAND[15:14]==2'b00);
    cover (dut.write && dut.COMMAND[15:12]==4'b1000);
    cover (dut.write && dut.COMMAND[15:11]==5'b10011);
    cover (dut.write && dut.COMMAND[15:11]==5'b10101);

    // Exercise cond/op2 extremes
    cover (dut.cond==3'b000);
    cover (dut.cond==3'b111);
    cover (dut.op2==3'b000);
    cover (dut.op2==3'b111);
  end

endmodule

bind DecodeUnit DecodeUnit_sva dut_sva();