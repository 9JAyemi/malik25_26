// SVA checker and bind for controlunit
// Focused, high-quality decode checks, safety properties, and concise coverage.

module controlunit_sva(
  input  logic [5:0] imemout,
  input  logic       brnch, memorywrite, memoryread, alusrc, regw, regdst, aluop, memtoreg
);

  function automatic logic [7:0] decode(input logic [5:0] op);
    case (op)
      6'b000000: decode = 8'b00001111; // R-type
      6'b100011: decode = 8'b00111000; // LW
      6'b101011: decode = 8'b01010000; // SW
      6'b000100: decode = 8'b10000000; // BEQ
      default  : decode = 8'b00000000; // default
    endcase
  endfunction

  logic [7:0] outv;
  assign outv = {brnch, memorywrite, memoryread, alusrc, regw, regdst, aluop, memtoreg};

  // Golden decode equivalence (combinational)
  always_comb begin
    assert (outv === decode(imemout))
      else $error("controlunit decode mismatch: op=%b exp=%b got=%b", imemout, decode(imemout), outv);
  end

  // Safety/consistency
  always_comb begin
    assert (!$isunknown(outv)) else $error("controlunit: X/Z on outputs");
    assert (!(memorywrite && memoryread)) else $error("controlunit: memread & memwrite both 1");
    assert (!brnch || (memorywrite==0 && memoryread==0 && regw==0 && alusrc==0 && regdst==0 && aluop==0 && memtoreg==0))
      else $error("controlunit: branch must zero other controls");
    assert (!alusrc || (memoryread || memorywrite))
      else $error("controlunit: alusrc implies lw/sw");
    assert (!regdst   || (imemout==6'b000000)) else $error("controlunit: regdst only in R-type");
    assert (!aluop    || (imemout==6'b000000)) else $error("controlunit: aluop only in R-type");
    assert (!memtoreg || (imemout==6'b000000)) else $error("controlunit: memtoreg only in R-type");
    assert (!regw || (imemout==6'b000000 || imemout==6'b100011))
      else $error("controlunit: regw only in R-type or lw");
  end

  // Concise functional coverage
  always_comb begin
    cover (imemout == 6'b000000); // R
    cover (imemout == 6'b100011); // LW
    cover (imemout == 6'b101011); // SW
    cover (imemout == 6'b000100); // BEQ
    cover (!(imemout inside {6'b000000,6'b100011,6'b101011,6'b000100}) && outv==8'b0); // default path
  end

  // Ensure each control asserts at least once
  always_comb begin
    cover (brnch);
    cover (memorywrite);
    cover (memoryread);
    cover (alusrc);
    cover (regw);
    cover (regdst);
    cover (aluop);
    cover (memtoreg);
  end

endmodule

bind controlunit controlunit_sva controlunit_sva_i(
  .imemout(imemout),
  .brnch(brnch),
  .memorywrite(memorywrite),
  .memoryread(memoryread),
  .alusrc(alusrc),
  .regw(regw),
  .regdst(regdst),
  .aluop(aluop),
  .memtoreg(memtoreg)
);