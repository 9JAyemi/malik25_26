// SVA checker for control. Bind this to the DUT.
module control_sva (
  input  logic [2:0] OP,
  input  logic       CISEL,
  input  logic       BSEL,
  input  logic [1:0] OSEL,
  input  logic       SHIFT_LA,
  input  logic       SHIFT_LR,
  input  logic       LOGICAL_OP
);
  localparam [2:0] ADD=3'b000, SUB=3'b001, SRA=3'b010, SRL=3'b011,
                   SLL=3'b100, AND=3'b101, OR_=3'b110;

  // Basic sanity
  always @* begin
    assert (!$isunknown({OP,CISEL,BSEL,OSEL,SHIFT_LA,SHIFT_LR,LOGICAL_OP}))
      else $error("control: X/Z detected on signals");
    assert (CISEL===BSEL) else $error("control: CISEL and BSEL must match");
    assert (CISEL==(OP==SUB)) else $error("control: CISEL mismatch for OP");
    assert (BSEL==(OP==SUB)) else $error("control: BSEL mismatch for OP");
  end

  // Exact decode checks per opcode + coverage
  always @* begin
    case (OP)
      ADD: begin
        assert (OSEL==2'b00 && !SHIFT_LA && !SHIFT_LR && !LOGICAL_OP)
          else $error("control: ADD decode mismatch");
        cover (1);
      end
      SUB: begin
        assert (OSEL==2'b00 && !SHIFT_LA && !SHIFT_LR && !LOGICAL_OP)
          else $error("control: SUB decode mismatch");
        cover (1);
      end
      SRA: begin
        assert (OSEL==2'b01 &&  SHIFT_LA &&  SHIFT_LR && !LOGICAL_OP)
          else $error("control: SRA decode mismatch");
        cover (1);
      end
      SRL: begin
        assert (OSEL==2'b01 && !SHIFT_LA &&  SHIFT_LR && !LOGICAL_OP)
          else $error("control: SRL decode mismatch");
        cover (1);
      end
      SLL: begin
        assert (OSEL==2'b01 &&  SHIFT_LA && !SHIFT_LR && !LOGICAL_OP)
          else $error("control: SLL decode mismatch");
        cover (1);
      end
      AND: begin
        assert (OSEL==2'b10 && !SHIFT_LA && !SHIFT_LR &&  LOGICAL_OP)
          else $error("control: AND decode mismatch");
        cover (1);
      end
      OR_: begin
        assert (OSEL==2'b10 && !SHIFT_LA && !SHIFT_LR && !LOGICAL_OP)
          else $error("control: OR decode mismatch");
        cover (1);
      end
      default: begin
        assert (OSEL==2'b11 && !SHIFT_LA && !SHIFT_LR && !LOGICAL_OP)
          else $error("control: default decode mismatch");
        cover (1);
      end
    endcase
  end

  // Reverse-direction guards (outputs imply valid OP category)
  always @* begin
    assert (OSEL!=2'b00 || (OP inside {ADD,SUB}))
      else $error("control: OSEL=00 with invalid OP");
    assert (OSEL!=2'b01 || (OP inside {SRA,SRL,SLL}))
      else $error("control: OSEL=01 with invalid OP");
    assert (OSEL!=2'b10 || (OP inside {AND,OR_}))
      else $error("control: OSEL=10 with invalid OP");
    assert (OSEL!=2'b11 || (OP==3'b111))
      else $error("control: OSEL=11 should only occur on default/111");

    assert (!(SHIFT_LA && SHIFT_LR) || (OP==SRA))
      else $error("control: SHIFT_LA&SHIFT_LR only allowed for SRA");
    assert (!SHIFT_LR || (OP inside {SRA,SRL}))
      else $error("control: SHIFT_LR implies SRA/SRL");
    assert (!SHIFT_LA || (OP inside {SRA,SLL}))
      else $error("control: SHIFT_LA implies SRA/SLL");
    assert (!LOGICAL_OP || (OP==AND))
      else $error("control: LOGICAL_OP high must be AND");
  end

  // Functional coverage of each OP value and default
  always @* begin
    cover (OP==ADD);
    cover (OP==SUB);
    cover (OP==SRA);
    cover (OP==SRL);
    cover (OP==SLL);
    cover (OP==AND);
    cover (OP==OR_);
    cover (OP==3'b111);
  end
endmodule

// Bind into the DUT
bind control control_sva control_sva_i (.*);