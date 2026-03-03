// SVA checker for alu2. Bind this into the DUT.
// Purely combinational: uses immediate assertions and covers.
module alu2_sva(
  input  logic [31:0] srca,
  input  logic [31:0] srcb,
  input  logic [1:0]  alucontrol,
  input  logic [31:0] aluresult,
  input  logic [3:0]  aluflags
);
  logic [31:0] beff;
  logic        cin;
  logic [32:0] sum33;
  logic [31:0] exp_result;
  logic        exp_C, exp_V, exp_N, exp_Z;

  always @* begin
    beff      = alucontrol[0] ? ~srcb : srcb;
    cin       = alucontrol[0];
    sum33     = {1'b0,srca} + {1'b0,beff} + cin;

    unique case (alucontrol)
      2'b00, 2'b01: exp_result = sum33[31:0];
      2'b10:        exp_result = srca & srcb;
      2'b11:        exp_result = srca | srcb;
      default:      exp_result = 'x;
    endcase

    exp_C = (alucontrol[1]==1'b0) ? sum33[32] : 1'b0;

    if (alucontrol[1]==1'b0) begin
      // V for add/sub in 2's complement
      if (alucontrol[0]==1'b0)
        exp_V = (~(srca[31]^srcb[31])) & (exp_result[31]^srca[31]); // add
      else
        exp_V = ( (srca[31]^srcb[31])) & (exp_result[31]^srca[31]); // sub
    end else begin
      exp_V = 1'b0;
    end

    exp_N = exp_result[31];
    exp_Z = (exp_result==32'h0);

    // Core functional checks
    assert (aluresult === exp_result)
      else $error("ALU result mismatch: alucontrol=%b exp=%h got=%h", alucontrol, exp_result, aluresult);

    assert (aluflags[3] === exp_N)
      else $error("N flag mismatch: exp=%0b got=%0b", exp_N, aluflags[3]);

    assert (aluflags[2] === exp_Z)
      else $error("Z flag mismatch: exp=%0b got=%0b", exp_Z, aluflags[2]);

    assert (aluflags[1] === exp_C)
      else $error("C flag mismatch: alucontrol=%b exp=%0b got=%0b (carry=%0b)", alucontrol, exp_C, aluflags[1], sum33[32]);

    assert (aluflags[0] === exp_V)
      else $error("V flag mismatch: alucontrol=%b exp=%0b got=%0b", alucontrol, exp_V, aluflags[0]);

    // Flag gating on logic ops
    if (alucontrol[1]==1'b1) begin
      assert (aluflags[1]===1'b0) else $error("C should be 0 on logic ops");
      assert (aluflags[0]===1'b0) else $error("V should be 0 on logic ops");
    end

    // Concise coverage
    cover (alucontrol==2'b00);
    cover (alucontrol==2'b01);
    cover (alucontrol==2'b10);
    cover (alucontrol==2'b11);

    cover (alucontrol==2'b00 && exp_Z);
    cover (alucontrol==2'b01 && exp_Z);
    cover (alucontrol==2'b10 && exp_Z);
    cover (alucontrol==2'b11 && exp_Z);

    cover (alucontrol==2'b00 && exp_N);
    cover (alucontrol==2'b01 && exp_N);
    cover (alucontrol==2'b10 && exp_N);
    cover (alucontrol==2'b11 && exp_N);

    cover (alucontrol==2'b00 && exp_C);
    cover (alucontrol==2'b01 && exp_C);
    cover (alucontrol==2'b00 && exp_V);
    cover (alucontrol==2'b01 && exp_V);

    // Useful corner cases
    cover (alucontrol==2'b00 && srca==32'h7fffffff && srcb==32'h00000001 && exp_V);
    cover (alucontrol==2'b01 && srca==32'h80000000 && srcb==32'h00000001 && exp_V);
    cover (alucontrol==2'b10 && srca==32'hffff_ffff && srcb==32'h0000_0000 && exp_result==32'h0000_0000);
    cover (alucontrol==2'b11 && srca==32'h0000_0000 && srcb==32'hffff_ffff && exp_result==32'hffff_ffff);
  end
endmodule

// Bind into DUT (instance or module)
bind alu2 alu2_sva u_alu2_sva(
  .srca(srca),
  .srcb(srcb),
  .alucontrol(alucontrol),
  .aluresult(aluresult),
  .aluflags(aluflags)
);