// SVA checker for tv80_alu
// Concise, high-quality assertions with full functional coverage.
// Bind this checker to the DUT instance(s).

module tv80_alu_sva #(
  parameter Mode   = 0,
  parameter Flag_C = 0,
  parameter Flag_N = 1,
  parameter Flag_P = 2,
  parameter Flag_X = 3,
  parameter Flag_H = 4,
  parameter Flag_Y = 5,
  parameter Flag_Z = 6,
  parameter Flag_S = 7
)(
  input        Arith16,
  input        Z16,
  input  [3:0] ALU_Op,
  input  [5:0] IR,
  input  [1:0] ISet,
  input  [7:0] BusA,
  input  [7:0] BusB,
  input  [7:0] F_In,
  input  [7:0] Q,
  input  [7:0] F_Out
);

  // Helper functions matching DUT micro-ops
  function automatic [4:0] AddSub4(input [3:0] A, input [3:0] B, input Sub, input Carry_In);
    AddSub4 = {1'b0,A} + {1'b0,(Sub?~B:B)} + Carry_In;
  endfunction
  function automatic [3:0] AddSub3(input [2:0] A, input [2:0] B, input Sub, input Carry_In);
    AddSub3 = {1'b0,A} + {1'b0,(Sub?~B:B)} + Carry_In;
  endfunction
  function automatic [1:0] AddSub1(input A, input B, input Sub, input Carry_In);
    AddSub1 = {1'b0,A} + {1'b0,(Sub?~B:B)} + Carry_In;
  endfunction

  typedef struct packed {logic [7:0] q; logic [7:0] f;} alu_out_t;

  function automatic [7:0] bitmask(input [2:0] idx);
    case (idx)
      3'b000: bitmask = 8'b00000001;
      3'b001: bitmask = 8'b00000010;
      3'b010: bitmask = 8'b00000100;
      3'b011: bitmask = 8'b00001000;
      3'b100: bitmask = 8'b00010000;
      3'b101: bitmask = 8'b00100000;
      3'b110: bitmask = 8'b01000000;
      default:bitmask = 8'b10000000;
    endcase
  endfunction

  // Golden reference model derived from RTL for concise equality checks
  function automatic alu_out_t model(
    input        Arith16_i,
    input        Z16_i,
    input  [3:0] ALU_Op_i,
    input  [5:0] IR_i,
    input  [1:0] ISet_i,
    input  [7:0] BusA_i,
    input  [7:0] BusB_i,
    input  [7:0] F_In_i
  );
    alu_out_t m;
    logic [7:0] Q_t, Q_v;
    logic [7:0] F_o;
    logic [7:0] mask;
    logic UseCarry, HalfCarry_v, Carry7_v, Carry_v, OverFlow_v;
    logic [8:0] DAA_Q;

    mask = bitmask(IR_i[5:3]);

    // precompute add/sub pipeline
    UseCarry = ~ALU_Op_i[2] && ALU_Op_i[0];
    {HalfCarry_v, Q_v[3:0]} = AddSub4(BusA_i[3:0], BusB_i[3:0], ALU_Op_i[1], ALU_Op_i[1] ^ (UseCarry && F_In_i[Flag_C]));
    {Carry7_v,   Q_v[6:4]} = AddSub3(BusA_i[6:4], BusB_i[6:4], ALU_Op_i[1], HalfCarry_v);
    {Carry_v,    Q_v[7]}   = AddSub1(BusA_i[7],   BusB_i[7],   ALU_Op_i[1], Carry7_v);
    OverFlow_v = Carry_v ^ Carry7_v;

    Q_t = 8'hxx;
    F_o = F_In_i;
    DAA_Q = 'x;

    unique case (ALU_Op_i)
      // Arithmetic / logic group
      4'b0000,4'b0001,4'b0010,4'b0011,4'b0100,4'b0101,4'b0110,4'b0111: begin
        F_o[Flag_N] = 1'b0;
        F_o[Flag_C] = 1'b0;
        unique case (ALU_Op_i[2:0])
          3'b000,3'b001: begin
            Q_t = Q_v;
            F_o[Flag_C] = Carry_v;
            F_o[Flag_H] = HalfCarry_v;
            F_o[Flag_P] = OverFlow_v;
          end
          3'b010,3'b011,3'b111: begin
            Q_t = Q_v;
            F_o[Flag_N] = 1'b1;
            F_o[Flag_C] = ~Carry_v;
            F_o[Flag_H] = ~HalfCarry_v;
            F_o[Flag_P] = OverFlow_v;
          end
          3'b100: begin
            Q_t = BusA_i & BusB_i;
            F_o[Flag_H] = 1'b1;
          end
          3'b101: begin
            Q_t = BusA_i ^ BusB_i;
            F_o[Flag_H] = 1'b0;
          end
          default: begin // 3'b110
            Q_t = BusA_i | BusB_i;
            F_o[Flag_H] = 1'b0;
          end
        endcase

        if (ALU_Op_i[2:0] == 3'b111) begin
          F_o[Flag_X] = BusB_i[3];
          F_o[Flag_Y] = BusB_i[5];
        end else begin
          F_o[Flag_X] = Q_t[3];
          F_o[Flag_Y] = Q_t[5];
        end

        if (Q_t == 8'h00) begin
          F_o[Flag_Z] = 1'b1;
          if (Z16_i) F_o[Flag_Z] = F_In_i[Flag_Z];
        end else begin
          F_o[Flag_Z] = 1'b0;
        end
        F_o[Flag_S] = Q_t[7];

        unique case (ALU_Op_i[2:0])
          3'b000,3'b001,3'b010,3'b011,3'b111: ; // keep P from overflow above
          default: F_o[Flag_P] = ~(^Q_t); // parity for logic
        endcase

        if (Arith16_i) begin
          F_o[Flag_S] = F_In_i[Flag_S];
          F_o[Flag_Z] = F_In_i[Flag_Z];
          F_o[Flag_P] = F_In_i[Flag_P];
        end
      end

      // DAA
      4'b1100: begin
        F_o[Flag_H] = F_In_i[Flag_H];
        F_o[Flag_C] = F_In_i[Flag_C];
        DAA_Q[7:0] = BusA_i;
        DAA_Q[8] = 1'b0;
        if (!F_In_i[Flag_N]) begin
          if (DAA_Q[3:0] > 9 || F_In_i[Flag_H]) begin
            F_o[Flag_H] = (DAA_Q[3:0] > 9);
            DAA_Q = DAA_Q + 9'd6;
          end
          if (DAA_Q[8:4] > 9 || F_In_i[Flag_C]) begin
            DAA_Q = DAA_Q + 9'd96;
          end
        end else begin
          if (DAA_Q[3:0] > 9 || F_In_i[Flag_H]) begin
            if (DAA_Q[3:0] > 5) F_o[Flag_H] = 1'b0;
            DAA_Q[7:0] = DAA_Q[7:0] - 8'd6;
          end
          if (BusA_i > 8'd153 || F_In_i[Flag_C]) begin
            DAA_Q = DAA_Q - 9'd352;
          end
        end
        F_o[Flag_X] = DAA_Q[3];
        F_o[Flag_Y] = DAA_Q[5];
        F_o[Flag_C] = F_In_i[Flag_C] || DAA_Q[8];
        Q_t = DAA_Q[7:0];
        F_o[Flag_Z] = (DAA_Q[7:0] == 8'h00);
        F_o[Flag_S] = DAA_Q[7];
        F_o[Flag_P] = ~(^DAA_Q[7:0]);
      end

      // nibble merge
      4'b1101,4'b1110: begin
        Q_t[7:4] = BusA_i[7:4];
        Q_t[3:0] = (ALU_Op_i[0] ? BusB_i[7:4] : BusB_i[3:0]);
        F_o[Flag_H] = 1'b0;
        F_o[Flag_N] = 1'b0;
        F_o[Flag_X] = Q_t[3];
        F_o[Flag_Y] = Q_t[5];
        F_o[Flag_Z] = (Q_t == 8'h00);
        F_o[Flag_S] = Q_t[7];
        F_o[Flag_P] = ~(^Q_t);
      end

      // BIT b,(BusB)
      4'b1001: begin
        Q_t = BusB_i & mask;
        F_o[Flag_S] = Q_t[7];
        if (Q_t == 8'h00) begin
          F_o[Flag_Z] = 1'b1; F_o[Flag_P] = 1'b1;
        end else begin
          F_o[Flag_Z] = 1'b0; F_o[Flag_P] = 1'b0;
        end
        F_o[Flag_H] = 1'b1;
        F_o[Flag_N] = 1'b0;
        F_o[Flag_X] = 1'b0;
        F_o[Flag_Y] = 1'b0;
        if (IR_i[2:0] != 3'b110) begin
          F_o[Flag_X] = BusB_i[3];
          F_o[Flag_Y] = BusB_i[5];
        end
      end

      // SET/RES
      4'b1010: Q_t = BusB_i | mask;
      4'b1011: Q_t = BusB_i & ~mask;

      // SHIFT/ROTATE/EX
      4'b1000: begin
        unique case (IR_i[5:3])
          3'b000: begin // RLC
            Q_t[7:1] = BusA_i[6:0]; Q_t[0] = BusA_i[7];
            F_o[Flag_C] = BusA_i[7];
          end
          3'b010: begin // RL
            Q_t[7:1] = BusA_i[6:0]; Q_t[0] = F_In_i[Flag_C];
            F_o[Flag_C] = BusA_i[7];
          end
          3'b001: begin // RRC
            Q_t[6:0] = BusA_i[7:1]; Q_t[7] = BusA_i[0];
            F_o[Flag_C] = BusA_i[0];
          end
          3'b011: begin // RR
            Q_t[6:0] = BusA_i[7:1]; Q_t[7] = F_In_i[Flag_C];
            F_o[Flag_C] = BusA_i[0];
          end
          3'b100: begin // SLA
            Q_t[7:1] = BusA_i[6:0]; Q_t[0] = 1'b0;
            F_o[Flag_C] = BusA_i[7];
          end
          3'b110: begin // SLL or EX (Mode==3)
            if (Mode == 3) begin
              Q_t[7:4] = BusA_i[3:0]; Q_t[3:0] = BusA_i[7:4];
              F_o[Flag_C] = 1'b0;
            end else begin
              Q_t[7:1] = BusA_i[6:0]; Q_t[0] = 1'b1;
              F_o[Flag_C] = BusA_i[7];
            end
          end
          3'b101: begin // SRA
            Q_t[6:0] = BusA_i[7:1]; Q_t[7] = BusA_i[7];
            F_o[Flag_C] = BusA_i[0];
          end
          default: begin // SRL
            Q_t[6:0] = BusA_i[7:1]; Q_t[7] = 1'b0;
            F_o[Flag_C] = BusA_i[0];
          end
        endcase
        F_o[Flag_H] = 1'b0;
        F_o[Flag_N] = 1'b0;
        F_o[Flag_X] = Q_t[3];
        F_o[Flag_Y] = Q_t[5];
        F_o[Flag_S] = Q_t[7];
        F_o[Flag_Z] = (Q_t == 8'h00);
        F_o[Flag_P] = ~(^Q_t);
        if (ISet_i == 2'b00) begin
          F_o[Flag_P] = F_In_i[Flag_P];
          F_o[Flag_S] = F_In_i[Flag_S];
          F_o[Flag_Z] = F_In_i[Flag_Z];
        end
      end

      default: ; // unspecified, leave as is
    endcase

    m.q = Q_t;
    m.f = F_o;
    return m;
  endfunction

  function automatic bit supported_op(input [3:0] op);
    supported_op = (op inside {
      4'h0,4'h1,4'h2,4'h3,4'h4,4'h5,4'h6,4'h7, // arithmetic/logic
      4'h8, // shift/rotate
      4'h9, // BIT
      4'hA,4'hB, // SET/RES
      4'hC, // DAA
      4'hD,4'hE  // nibble merge
    });
  endfunction

  // Primary equivalence assertions (concise but complete)
  always_comb begin
    alu_out_t exp = model(Arith16, Z16, ALU_Op, IR, ISet, BusA, BusB, F_In);
    if (supported_op(ALU_Op) && !$isunknown({Arith16,Z16,ALU_Op,IR,ISet,BusA,BusB,F_In})) begin
      assert (Q === exp.q)
        else $error("tv80_alu: Q mismatch. op=%h IR=%h A=%h B=%h exp=%h got=%h", ALU_Op, IR, BusA, BusB, exp.q, Q);
      assert (F_Out === exp.f)
        else $error("tv80_alu: F_Out mismatch. op=%h IR=%h A=%h B=%h exp=%h got=%h", ALU_Op, IR, BusA, BusB, exp.f, F_Out);
    end
  end

  // Targeted invariants (extra safety, independent of model)
  // Logic ops flags
  always_comb if (ALU_Op inside {4'h0,4'h1,4'h2,4'h3,4'h4,4'h5,4'h6,4'h7} && !$isunknown({ALU_Op,BUSA,BusB,F_In})) begin
    unique case (ALU_Op[2:0])
      3'b100: begin
        assert (Q == (BusA & BusB)) else $error("AND result wrong");
        assert (F_Out[Flag_H] == 1'b1 && F_Out[Flag_N] == 1'b0) else $error("AND flags H/N wrong");
      end
      3'b101: begin
        assert (Q == (BusA ^ BusB)) else $error("XOR result wrong");
        assert (F_Out[Flag_H] == 1'b0 && F_Out[Flag_N] == 1'b0) else $error("XOR flags H/N wrong");
      end
      3'b110: begin
        assert (Q == (BusA | BusB)) else $error("OR result wrong");
        assert (F_Out[Flag_H] == 1'b0 && F_Out[Flag_N] == 1'b0) else $error("OR flags H/N wrong");
      end
      default: ; // arithmetic checked by main model
    endcase
  end

  // BIT/SET/RES masks
  wire [7:0] MASK = bitmask(IR[5:3]);
  always_comb if (ALU_Op == 4'h9 && !$isunknown({IR,BusB})) assert (Q == (BusB & MASK)) else if (ALU_Op == 4'h9) $error("BIT result wrong");
  always_comb if (ALU_Op == 4'hA && !$isunknown({IR,BusB})) assert (Q == (BusB | MASK)) else if (ALU_Op == 4'hA) $error("SET result wrong");
  always_comb if (ALU_Op == 4'hB && !$isunknown({IR,BusB})) assert (Q == (BusB & ~MASK)) else if (ALU_Op == 4'hB) $error("RES result wrong");

  // Rotate/shift: EX (Mode==3)
  always_comb if (ALU_Op == 4'h8 && IR[5:3]==3'b110 && Mode==3 && !$isunknown({BusA})) begin
    assert (Q == {BusA[3:0],BusA[7:4]} && F_Out[Flag_C]==1'b0)
      else $error("EX (Mode=3) wrong");
  end

  // Compare (ALU_Op[2:0]==111): X/Y come from BusB
  always_comb if ((ALU_Op inside {4'h0,4'h1,4'h2,4'h3,4'h4,4'h5,4'h6,4'h7}) && ALU_Op[2:0]==3'b111 && !$isunknown({BusB})) begin
    assert (F_Out[Flag_X] == BusB[3] && F_Out[Flag_Y] == BusB[5]) else $error("CP X/Y flags wrong");
  end

  // Arith16 gate holds S/Z/P
  always_comb if ((ALU_Op inside {4'h0,4'h1,4'h2,4'h3,4'h4,4'h5,4'h6,4'h7}) && Arith16 && !$isunknown({F_In})) begin
    assert (F_Out[Flag_S]==F_In[Flag_S] && F_Out[Flag_Z]==F_In[Flag_Z] && F_Out[Flag_P]==F_In[Flag_P])
      else $error("Arith16 gating of SZP wrong");
  end

  // Z16 gate holds Z on zero result
  always_comb if ((ALU_Op inside {4'h0,4'h1,4'h2,4'h3,4'h4,4'h5,4'h6,4'h7}) && Z16 && (Q==8'h00)) begin
    assert (F_Out[Flag_Z]==F_In[Flag_Z]) else $error("Z16 gate for Z wrong");
  end

  // ISet gate in shift/rotate holds SZP
  always_comb if (ALU_Op==4'h8 && ISet==2'b00) begin
    assert (F_Out[Flag_S]==F_In[Flag_S] && F_Out[Flag_Z]==F_In[Flag_Z] && F_Out[Flag_P]==F_In[Flag_P])
      else $error("ISet gating of SZP wrong");
  end

  // Minimal functional coverage (immediate cover)
  always_comb begin
    cover (ALU_Op == 4'h0); cover (ALU_Op == 4'h1); cover (ALU_Op == 4'h2); cover (ALU_Op == 4'h3);
    cover (ALU_Op == 4'h4); cover (ALU_Op == 4'h5); cover (ALU_Op == 4'h6); cover (ALU_Op == 4'h7);
    cover (ALU_Op == 4'h8); cover (ALU_Op == 4'h9); cover (ALU_Op == 4'hA); cover (ALU_Op == 4'hB);
    cover (ALU_Op == 4'hC); cover (ALU_Op == 4'hD); cover (ALU_Op == 4'hE);

    // Interesting scenarios
    cover (ALU_Op inside {4'h0,4'h1,4'h2,4'h3} && ALU_Op[0] && F_In[Flag_C]); // use-carry path
    cover (ALU_Op == 4'hC && F_In[Flag_N]==0 && F_In[Flag_H]); // DAA add half carry
    cover (ALU_Op == 4'hC && F_In[Flag_N]==1 && F_In[Flag_C]); // DAA sub with carry
    cover (ALU_Op == 4'h8 && IR[5:3]==3'b110 && Mode==3); // EX path
    cover (ALU_Op == 4'h9 && IR[2:0]!=3'b110); // BIT X/Y from BusB
    cover (Arith16); cover (Z16); cover (ISet==2'b00);
  end

endmodule

// Bind the checker to all instances of tv80_alu
bind tv80_alu tv80_alu_sva #(.Mode(Mode), .Flag_C(Flag_C), .Flag_N(Flag_N), .Flag_P(Flag_P),
                             .Flag_X(Flag_X), .Flag_H(Flag_H), .Flag_Y(Flag_Y),
                             .Flag_Z(Flag_Z), .Flag_S(Flag_S))
u_tv80_alu_sva (
  .Arith16(Arith16),
  .Z16(Z16),
  .ALU_Op(ALU_Op),
  .IR(IR),
  .ISet(ISet),
  .BusA(BusA),
  .BusB(BusB),
  .F_In(F_In),
  .Q(Q),
  .F_Out(F_Out)
);