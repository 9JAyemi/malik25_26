// Bindable SVA checker for ALU (combinational, zero-delay settle)
// Uses immediate assertions in an @* with #0 to sample post-settle.
// Concise, full functional checks per opcode + focused coverage.

module alu_sva_checker
(
  input logic [31:0] A,
  input logic [31:0] B,
  input logic [4:0]  ALUOp,
  input logic [31:0] ALUOut,
  input logic        Zero
);
  // Mirror opcodes from DUT
  localparam int ADD  = 5'd0;
  localparam int SUB  = 5'd1;
  localparam int ADDI = 5'd2;
  localparam int SUBI = 5'd3;
  localparam int MLT  = 5'd4;
  localparam int MLTI = 5'd5;
  localparam int AND_ = 5'd6;
  localparam int OR_  = 5'd7;
  localparam int ANDI = 5'd8;
  localparam int ORI  = 5'd9;
  localparam int SLR  = 5'd10;
  localparam int SLL  = 5'd11;
  localparam int LDR  = 5'd12;
  localparam int STR  = 5'd13;
  localparam int BNE  = 5'd14;
  localparam int BEQ  = 5'd15;
  localparam int J    = 5'd16;   // falls into default in RTL
  localparam int CMP  = 5'd17;
  localparam int NOP  = 5'd31;   // falls into default in RTL

  // Helper to keep messages concise
  `define AERR(msg) \
    begin $error("ALU SVA: %s (A=0x%08h B=0x%08h op=%0d out=0x%08h Z=%0b)", msg, A, B, ALUOp, ALUOut, Zero); end

  always @* begin
    // allow combinational logic to settle
    #0;

    // Basic X/Z check on key signals
    assert (!$isunknown({A,B,ALUOp,ALUOut,Zero})) else `AERR("X/Z detected");

    // Functional checks grouped by behavior
    if (ALUOp inside {ADD, ADDI, LDR, STR}) begin
      assert (ALUOut == (A + B) && Zero == 1'b0) else `AERR("ADD-like op fail (A+B, Z=0)");
    end
    else if (ALUOp inside {SUB, SUBI}) begin
      assert (ALUOut == (A - B) && Zero == 1'b0) else `AERR("SUB-like op fail (A-B, Z=0)");
    end
    else if (ALUOp inside {MLT, MLTI}) begin
      assert (ALUOut == (A * B) && Zero == 1'b0) else `AERR("MLT-like op fail (A*B, Z=0)");
    end
    else if (ALUOp inside {AND_, ANDI}) begin
      assert (ALUOut == (A & B) && Zero == 1'b0) else `AERR("AND-like op fail (A&B, Z=0)");
    end
    else if (ALUOp inside {OR_, ORI}) begin
      assert (ALUOut == (A | B) && Zero == 1'b0) else `AERR("OR-like op fail (A|B, Z=0)");
    end
    else if (ALUOp == SLR) begin
      assert (ALUOut == (A >> B) && Zero == 1'b0) else `AERR("SLR fail (A>>B, Z=0)");
    end
    else if (ALUOp == SLL) begin
      assert (ALUOut == (A << B) && Zero == 1'b0) else `AERR("SLL fail (A<<B, Z=0)");
    end
    else if (ALUOp inside {BEQ, BNE}) begin
      assert (ALUOut == 32'd0 && Zero == (A==B)) else `AERR("BEQ/BNE fail (out=0, Z=(A==B))");
    end
    else if (ALUOp == CMP) begin
      assert ( (A >  B && ALUOut == 32'd1) ||
               (A == B && ALUOut == 32'd0) ||
               (A <  B && ALUOut == 32'd2) ) else `AERR("CMP fail (out: gt=1 eq=0 lt=2)");
      assert (Zero == 1'b0) else `AERR("CMP Zero flag must be 0");
    end
    else begin
      // default (includes J, NOP, and any undefined opcode)
      assert (ALUOut == 32'd0 && Zero == 1'b0) else `AERR("default/NOP/J fail (out=0, Z=0)");
    end

    // Compact functional coverage (hit every opcode and key corners)
    cover (ALUOp == ADD);  cover (ALUOp == SUB);
    cover (ALUOp == ADDI); cover (ALUOp == SUBI);
    cover (ALUOp == MLT);  cover (ALUOp == MLTI);
    cover (ALUOp == AND_); cover (ALUOp == ANDI);
    cover (ALUOp == OR_);  cover (ALUOp == ORI);
    cover (ALUOp == SLR);  cover (ALUOp == SLL);
    cover (ALUOp == LDR);  cover (ALUOp == STR);
    cover (ALUOp == BEQ);  cover (ALUOp == BNE);
    cover (ALUOp == CMP);  cover (ALUOp == J);
    cover (ALUOp == NOP);

    cover (ALUOp inside {BEQ,BNE} && (A==B));
    cover (ALUOp inside {BEQ,BNE} && (A!=B));
    cover (ALUOp == CMP && A>B);
    cover (ALUOp == CMP && A==B);
    cover (ALUOp == CMP && A<B);
    cover (ALUOp inside {SLL,SLR} && B==0);
    cover (ALUOp inside {SLL,SLR} && B>=32);
  end

endmodule

// Bind into DUT (instance name will depend on your environment)
bind ALU alu_sva_checker u_alu_sva_checker (.A(A), .B(B), .ALUOp(ALUOp), .ALUOut(ALUOut), .Zero(Zero));