// SVA bind for Instruction_Mem. Concise, full functional check + coverage.
module Instruction_Mem_sva(input logic [15:0] PCAdress,
                           input logic [15:0] Instruction_out);

  function automatic logic [15:0] exp_instr(input logic [15:0] addr);
    unique case (addr)
      16'h0000: exp_instr = 16'hc000;
      16'h0001: exp_instr = 16'ha802;
      16'h0002: exp_instr = 16'hc66b;
      16'h0003: exp_instr = 16'hec00;
      16'h0004: exp_instr = 16'hd119;
      16'h0005: exp_instr = 16'h6895;
      16'h0006: exp_instr = 16'h6805;
      16'h0007: exp_instr = 16'h696d;
      16'h0008: exp_instr = 16'h68aa;
      16'h0009: exp_instr = 16'h7168;
      16'h000a: exp_instr = 16'h6805;
      16'h000b: exp_instr = 16'h7168;
      16'h000c: exp_instr = 16'h6895;
      16'h000d: exp_instr = 16'h6368;
      16'h000e: exp_instr = 16'h6802;
      16'h000f: exp_instr = 16'h6802;
      16'h0010: exp_instr = 16'ha818;
      16'h0011: exp_instr = 16'haa19;
      16'h0012: exp_instr = 16'had1a;
      16'h0013: exp_instr = 16'hf014;
      16'h0014: exp_instr = 16'ha003;
      16'h0015: exp_instr = 16'h4640;
      16'h0016: exp_instr = 16'h1901;
      16'h0017: exp_instr = 16'hb108;
      16'h0018: exp_instr = 16'h4640;
      16'h0019: exp_instr = 16'h1902;
      16'h001a: exp_instr = 16'hb110;
      16'h001b: exp_instr = 16'h4640;
      16'h001c: exp_instr = 16'h1904;
      16'h001d: exp_instr = 16'hb119;
      16'h001e: exp_instr = 16'h9b80;
      16'h001f: exp_instr = 16'hc000;
      16'h0020: exp_instr = 16'h5840;
      16'h0021: exp_instr = 16'h5888;
      16'h0022: exp_instr = 16'h58d0;
      16'h0023: exp_instr = 16'h5918;
      16'h0024: exp_instr = 16'h5960;
      16'h0025: exp_instr = 16'ha703;
      16'h0026: exp_instr = 16'h47f8;
      16'h0027: exp_instr = 16'h1f01;
      16'h0028: exp_instr = 16'hb7fd;
      16'h0029: exp_instr = 16'h9b80;
      16'h002a: exp_instr = 16'hc000;
      16'h002b: exp_instr = 16'h6400;
      16'h002c: exp_instr = 16'h5840;
      16'h002d: exp_instr = 16'h5888;
      16'h002e: exp_instr = 16'h58d0;
      16'h002f: exp_instr = 16'h5918;
      16'h0030: exp_instr = 16'h5960;
      16'h0031: exp_instr = 16'ha703;
      16'h0032: exp_instr = 16'h47f8;
      16'h0033: exp_instr = 16'h1f02;
      16'h0034: exp_instr = 16'hb7fd;
      16'h0035: exp_instr = 16'h9b80;
      16'h0036: exp_instr = 16'ha018;
      16'h0037: exp_instr = 16'ha219;
      16'h0038: exp_instr = 16'ha51a;
      16'h0039: exp_instr = 16'h5850;
      16'h003a: exp_instr = 16'h2940;
      16'h003b: exp_instr = 16'hf808;
      16'h003c: exp_instr = 16'h6c4f;
      16'h003d: exp_instr = 16'hf801;
      16'h003e: exp_instr = 16'h4ccf;
      16'h003f: exp_instr = 16'h6cdd;
      16'h0040: exp_instr = 16'h5900;
      16'h0041: exp_instr = 16'he800;
      16'h0042: exp_instr = 16'ha703;
      16'h0043: exp_instr = 16'h47f8;
      16'h0044: exp_instr = 16'h1f04;
      16'h0045: exp_instr = 16'hb7fd;
      16'h0046: exp_instr = 16'h9b80;
      default:  exp_instr = 16'h0000;
    endcase
  endfunction

  // Functional equivalence check (combinational, sampled post-update)
  property p_map;
    @(PCAdress) 1'b1 |-> ##0 (Instruction_out == exp_instr(PCAdress));
  endproperty
  assert property (p_map);

  // Output must never be X/Z after it updates
  assert property (@(Instruction_out) ##0 !$isunknown(Instruction_out));

  // Default-path coverage (upper byte nonzero or in-range-but-above-table)
  cover property (@(PCAdress)
                  ((PCAdress[15:8] != 8'h00) || (PCAdress[15:8] == 8'h00 && PCAdress[7:0] > 8'h46))
                  ##0 (Instruction_out == 16'h0000));

  // Per-address hit coverage (with correct data) for 0x0000..0x0046
  genvar i;
  generate
    for (i = 0; i <= 8'h46; i++) begin : C_ADDR
      localparam int unsigned IU = i;
      localparam logic [15:0] A = IU[15:0];
      cover property (@(PCAdress) (PCAdress == A) ##0 (Instruction_out == exp_instr(A)));
    end
  endgenerate

endmodule

bind Instruction_Mem Instruction_Mem_sva u_instruction_mem_sva(.PCAdress(PCAdress),
                                                               .Instruction_out(Instruction_out));