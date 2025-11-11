// SVA checker for ALU (bindable, no DUT changes needed)
module ALU_sva;
  // Fire an event on any combinational change; sample after settle using ##0
  event comb_ev; always @(*) -> comb_ev;
  default clocking cb @ (comb_ev); endclocking

  // Local helpers
  wire [3:0] ctrl = {alu_ctrl3, alu_ctrl2, alu_ctrl1, alu_ctrl0};

  function automatic [7:0] sat8_add(input [7:0] a, b);
    automatic logic [8:0] s; begin s = a + b; sat8_add = s[8] ? 8'hFF : s[7:0]; end
  endfunction
  function automatic [7:0] sub8(input [7:0] a, b);
    sub8 = a - b;
  endfunction
  function automatic bit add_ovf32(input logic [31:0] a,b,sum);
    add_ovf32 = (a[31]==b[31]) && (sum[31]!=a[31]);
  endfunction

  // Basic sanity
  assert property (!$isunknown(ctrl)) else $error("ALU ctrl has X/Z");
  assert property (##0 !$isunknown(alu_out)) else $error("ALU alu_out has X/Z");

  // Flag checks
  assert property (##0 flag_z == ~(|alu_out));
  assert property (##0 flag_n == alu_out[31]);
  assert property ((ctrl == ADD) |-> ##0 (flag_v == add_ovf32(in0, in1, alu_out)));

  // Result checks for each opcode
  assert property ((ctrl == ADD)  |-> ##0 (alu_out == (in0 + in1)));
  assert property ((ctrl == SUB)  |-> ##0 (alu_out == (in0 - in1)));
  assert property ((ctrl == LUI)  |-> ##0 (alu_out == {in1[15:0],16'h0000}));
  assert property ((ctrl == MOV)  |-> ##0 (alu_out == in0));
  assert property ((ctrl == AND)  |-> ##0 (alu_out == (in0 & in1)));
  assert property ((ctrl == OR)   |-> ##0 (alu_out == (in0 | in1)));
  assert property ((ctrl == XOR)  |-> ##0 (alu_out == (in0 ^ in1)));
  assert property ((ctrl == NOT)  |-> ##0 (alu_out == ~in0));

  assert property ((ctrl == SLL)  |-> ##0 (alu_out == (in0 << shamt)));
  assert property ((ctrl == SRL)  |-> ##0 (alu_out == (in0 >> shamt)));
  assert property ((ctrl == SRA)  |-> ##0 (alu_out == ($signed(in0) >>> shamt)));

  // Byte-wise saturated add
  assert property ((ctrl == ADDB)  |-> ##0 (alu_out ==
    { sat8_add(in0[31:24], in1[31:24]),
      sat8_add(in0[23:16], in1[23:16]),
      sat8_add(in0[15:8],  in1[15:8]),
      sat8_add(in0[7:0],   in1[7:0]) }));

  // Byte-wise saturated add-immediate (upper bytes use in0[15:8] and in1[7:0])
  assert property ((ctrl == ADDBI) |-> ##0 (alu_out ==
    { sat8_add(in0[15:8], in1[7:0]),
      sat8_add(in0[15:8], in1[7:0]),
      sat8_add(in0[15:8], in1[7:0]),
      sat8_add(in0[7:0],  in1[7:0]) }));

  // Byte-wise subtract (wrap in 8b)
  assert property ((ctrl == SUBB)  |-> ##0 (alu_out ==
    { sub8(in0[31:24], in1[31:24]),
      sub8(in0[23:16], in1[23:16]),
      sub8(in0[15:8],  in1[15:8]),
      sub8(in0[7:0],   in1[7:0]) }));

  // Byte-wise subtract-immediate (upper bytes use in0[15:8] and in1[7:0])
  assert property ((ctrl == SUBBI) |-> ##0 (alu_out ==
    { sub8(in0[15:8], in1[7:0]),
      sub8(in0[15:8], in1[7:0]),
      sub8(in0[15:8], in1[7:0]),
      sub8(in0[7:0],  in1[7:0]) }));

  // LLDC: load lower 16b from perf_cnt, zero-extend upper
  assert property ((ctrl == LLDC)  |-> ##0 (alu_out == {16'h0000, perf_cnt}));

  // Opcode coverage
  cover property (ctrl == ADD);
  cover property (ctrl == SUB);
  cover property (ctrl == LUI);
  cover property (ctrl == MOV);
  cover property (ctrl == AND);
  cover property (ctrl == SLL);
  cover property (ctrl == SRA);
  cover property (ctrl == SRL);
  cover property (ctrl == NOT);
  cover property (ctrl == OR);
  cover property (ctrl == XOR);
  cover property (ctrl == ADDB);
  cover property (ctrl == ADDBI);
  cover property (ctrl == SUBB);
  cover property (ctrl == SUBBI);
  cover property (ctrl == LLDC);

  // Corner-case coverage
  cover property ((ctrl == ADD)  && add_ovf32(in0, in1, in0 + in1));
  cover property ((ctrl == ADD)  && !add_ovf32(in0, in1, in0 + in1));
  cover property ((ctrl == ADDB) && (({1'b0,in0[7:0]}  + {1'b0,in1[7:0]})[8] ||
                                     ({1'b0,in0[15:8]} + {1'b0,in1[15:8]})[8] ||
                                     ({1'b0,in0[23:16]}+ {1'b0,in1[23:16]})[8] ||
                                     ({1'b0,in0[31:24]}+ {1'b0,in1[31:24]})[8]));
  cover property ((ctrl == ADDBI) && (({1'b0,in0[7:0]}  + {1'b0,in1[7:0]})[8] ||
                                      ({1'b0,in0[15:8]} + {1'b0,in1[7:0]})[8]));
  cover property ((ctrl == SLL) && (shamt == 5'd0));
  cover property ((ctrl == SLL) && (shamt == 5'd31));
  cover property ((ctrl == SRL) && (shamt == 5'd0));
  cover property ((ctrl == SRL) && (shamt == 5'd31));
  cover property ((ctrl == SRA) && (shamt == 5'd31) && in0[31]); // sign-propagation
endmodule

// Bind into DUT
bind ALU ALU_sva sva_i();