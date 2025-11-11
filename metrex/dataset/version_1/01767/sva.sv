// SVA checker for alu. Bind this to the DUT.
// Concise, full functional checks and focused coverage.
`ifndef ALU_SVA
`define ALU_SVA

module alu_sva (
  input logic [3:0]  ctl,
  input logic [31:0] a, b,
  input logic [31:0] out,
  input logic        zero
);
  logic [31:0] exp_add, exp_sub, exp_and, exp_or, exp_nor, exp_xor;
  logic        exp_slt_bit;
  logic        of_add, of_sub;

  always_comb begin
    exp_add     = a + b;
    exp_sub     = a - b;
    exp_and     = a & b;
    exp_or      = a | b;
    exp_nor     = ~(a | b);
    exp_xor     = a ^ b;
    exp_slt_bit = ($signed(a) < $signed(b));

    // Correct signed overflow indicators (for coverage)
    of_add = (a[31] == b[31]) && (exp_add[31] != a[31]);
    of_sub = (a[31] != b[31]) && (exp_sub[31] != a[31]);

    // Zero flag must reflect out==0
    assert (zero === (out == 32'h0))
      else $error("ALU zero flag mismatch: zero=%0b out=%h", zero, out);

    // Functional correctness per operation
    unique case (ctl)
      4'b0010: assert (out == exp_add)
                 else $error("ALU ADD mismatch: a=%h b=%h out=%h exp=%h", a, b, out, exp_add);
      4'b0000: assert (out == exp_and)
                 else $error("ALU AND mismatch: a=%h b=%h out=%h exp=%h", a, b, out, exp_and);
      4'b1100: assert (out == exp_nor)
                 else $error("ALU NOR mismatch: a=%h b=%h out=%h exp=%h", a, b, out, exp_nor);
      4'b0001: assert (out == exp_or )
                 else $error("ALU  OR mismatch: a=%h b=%h out=%h exp=%h", a, b, out, exp_or);
      4'b0111: begin
                 assert (out[31:1] == '0)
                   else $error("ALU SLT upper bits not zero: out=%h", out);
                 assert (out[0] == exp_slt_bit)
                   else $error("ALU SLT mismatch: a=%h b=%h out=%h exp_bit=%0b", a, b, out, exp_slt_bit);
               end
      4'b0110: assert (out == exp_sub)
                 else $error("ALU SUB mismatch: a=%h b=%h out=%h exp=%h", a, b, out, exp_sub);
      4'b1101: assert (out == exp_xor)
                 else $error("ALU XOR mismatch: a=%h b=%h out=%h exp=%h", a, b, out, exp_xor);
      default: assert (out == 32'h0)
                 else $error("ALU DEFAULT mismatch: ctl=%b out=%h exp=0", ctl, out);
    endcase

    // Minimal but meaningful coverage
    cover (ctl == 4'b0000);
    cover (ctl == 4'b0001);
    cover (ctl == 4'b0010);
    cover (ctl == 4'b0110);
    cover (ctl == 4'b0111);
    cover (ctl == 4'b1100);
    cover (ctl == 4'b1101);

    cover (ctl inside {4'b0010,4'b0110} && zero);   // arithmetic zero result
    cover (ctl == 4'b0010 && of_add);               // add overflow scenario
    cover (ctl == 4'b0110 && of_sub);               // sub overflow scenario
    cover (ctl == 4'b0111 && exp_slt_bit);          // slt true
    cover (ctl == 4'b0111 && !exp_slt_bit);         // slt false

    cover (ctl == 4'b0000 && zero);                 // AND -> 0
    cover (ctl == 4'b0001 && zero);                 // OR  -> 0
    cover (ctl == 4'b1100 && zero);                 // NOR -> 0
    cover (ctl == 4'b1101 && zero);                 // XOR -> 0
  end
endmodule

bind alu alu_sva u_alu_sva (.*);

`endif