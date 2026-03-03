// SVA for barrel_shifter_16bit
module barrel_shifter_16bit_sva(
  input logic               clk,
  input logic               rst_n,
  input logic [15:0]        D,
  input logic [3:0]         shift_ctrl,
  input logic [15:0]        Q
);
  default clocking cb @(posedge clk); endclocking

  function automatic [15:0] f_shift(input [15:0] d, input [3:0] c);
    unique case (c)
      4'b0000: f_shift = d << 1;
      4'b0001: f_shift = d << 2;
      4'b0010: f_shift = d << 4;
      4'b0011: f_shift = d << 8;
      4'b0100: f_shift = d >> 1;
      4'b0101: f_shift = d >> 2;
      4'b0110: f_shift = d >> 4;
      4'b0111: f_shift = d >> 8;
      default: f_shift = d;
    endcase
  endfunction

  // Functional equivalence and no-X on output when inputs known
  assert property (disable iff (!rst_n)
    !$isunknown({D,shift_ctrl}) |-> (Q == f_shift(D,shift_ctrl) && !$isunknown(Q))
  );

  // Decode coverage (each implemented op + default range)
  genvar i;
  generate for (i=0; i<8; i++) begin : g_cov_bs
    cover property (disable iff (!rst_n) !$isunknown({D,shift_ctrl}) && shift_ctrl == i[3:0]);
  end endgenerate
  cover property (disable iff (!rst_n) !$isunknown({D,shift_ctrl}) && (shift_ctrl inside {[4'h8:4'hF]}));
endmodule

// SVA for alu_32bit
module alu_32bit_sva(
  input logic               clk,
  input logic               rst_n,
  input logic [31:0]        a,
  input logic [31:0]        b,
  input logic [3:0]         ctrl,
  input logic [31:0]        result
);
  default clocking cb @(posedge clk); endclocking

  function automatic [31:0] f_alu(input [31:0] aa, input [31:0] bb, input [3:0] c);
    unique case (c)
      4'b0000: f_alu = aa + bb;
      4'b0001: f_alu = aa - bb;
      4'b0010: f_alu = aa & bb;
      4'b0011: f_alu = aa | bb;
      4'b0100: f_alu = aa ^ bb;
      default: f_alu = aa;
    endcase
  endfunction

  // Functional equivalence and no-X on output when inputs known
  assert property (disable iff (!rst_n)
    !$isunknown({a,b,ctrl}) |-> (result == f_alu(a,b,ctrl) && !$isunknown(result))
  );

  // Operation coverage (implemented ops + default range)
  genvar j;
  generate for (j=0; j<5; j++) begin : g_cov_alu
    cover property (disable iff (!rst_n) !$isunknown({a,b,ctrl}) && ctrl == j[3:0]);
  end endgenerate
  cover property (disable iff (!rst_n) !$isunknown({a,b,ctrl}) && (ctrl inside {[4'h5:4'hF]}));

  // Interesting arithmetic scenarios
  cover property (disable iff (!rst_n) !$isunknown({a,b}) && ctrl==4'b0000 && (f_alu(a,b,ctrl) < a)); // unsigned add overflow
  cover property (disable iff (!rst_n) !$isunknown({a,b}) && ctrl==4'b0001 && (f_alu(a,b,ctrl) > a)); // unsigned sub underflow
endmodule

// SVA for top_module (end-to-end)
module top_module_sva(
  input logic               clk,
  input logic               rst_n,
  input logic [15:0]        D,
  input logic [3:0]         shift_ctrl,
  input logic [31:0]        a,
  input logic [31:0]        b,
  input logic [3:0]         alu_ctrl,
  input logic [31:0]        result
);
  default clocking cb @(posedge clk); endclocking

  function automatic [15:0] f_shift(input [15:0] d, input [3:0] c);
    unique case (c)
      4'b0000: f_shift = d << 1;
      4'b0001: f_shift = d << 2;
      4'b0010: f_shift = d << 4;
      4'b0011: f_shift = d << 8;
      4'b0100: f_shift = d >> 1;
      4'b0101: f_shift = d >> 2;
      4'b0110: f_shift = d >> 4;
      4'b0111: f_shift = d >> 8;
      default: f_shift = d;
    endcase
  endfunction

  function automatic [31:0] f_alu(input [31:0] aa, input [31:0] bb, input [3:0] c);
    unique case (c)
      4'b0000: f_alu = aa + bb;
      4'b0001: f_alu = aa - bb;
      4'b0010: f_alu = aa & bb;
      4'b0011: f_alu = aa | bb;
      4'b0100: f_alu = aa ^ bb;
      default: f_alu = aa;
    endcase
  endfunction

  function automatic [31:0] f_top(
    input [15:0] d, input [3:0] sc,
    input [31:0] aa, input [31:0] bb, input [3:0] ac
  );
    automatic logic [15:0] sd = f_shift(d,sc);
    automatic logic [31:0] ar = f_alu(aa,bb,ac);
    f_top = ar | {16'b0, sd};
  endfunction

  // End-to-end functional equivalence and no-X on output when inputs known
  assert property (disable iff (!rst_n)
    !$isunknown({D,shift_ctrl,a,b,alu_ctrl}) |-> (result == f_top(D,shift_ctrl,a,b,alu_ctrl) && !$isunknown(result))
  );

  // Sanity: upper/lower OR structure preserved
  assert property (disable iff (!rst_n)
    !$isunknown({D,shift_ctrl,a,b,alu_ctrl}) |->
      (result[31:16] == f_alu(a,b,alu_ctrl)[31:16]) &&
      (result[15:0]  == (f_alu(a,b,alu_ctrl)[15:0] | f_shift(D,shift_ctrl)))
  );

  // Coverage: both defaults simultaneously exercised
  cover property (disable iff (!rst_n)
    !$isunknown({D,shift_ctrl,a,b,alu_ctrl}) &&
    (shift_ctrl inside {[4'h8:4'hF]}) && (alu_ctrl inside {[4'h5:4'hF]})
  );

  // Coverage: OR effect changes lower 16b due to shifter bits only
  cover property (disable iff (!rst_n)
    !$isunknown({D,shift_ctrl,a,b,alu_ctrl}) &&
    ((f_shift(D,shift_ctrl) & ~f_alu(a,b,alu_ctrl)[15:0]) != 16'b0)
  );

  // Coverage: OR effect masked by ALU lower bits already 1s
  cover property (disable iff (!rst_n)
    !$isunknown({D,shift_ctrl,a,b,alu_ctrl}) &&
    ((~f_shift(D,shift_ctrl) & f_alu(a,b,alu_ctrl)[15:0]) != 16'b0)
  );
endmodule

// Example binds (connect clk/rst from your TB)
bind barrel_shifter_16bit barrel_shifter_16bit_sva u_bs_sva(
  .clk(tb_clk), .rst_n(tb_rst_n), .D(D), .shift_ctrl(shift_ctrl), .Q(Q)
);
bind alu_32bit alu_32bit_sva u_alu_sva(
  .clk(tb_clk), .rst_n(tb_rst_n), .a(a), .b(b), .ctrl(ctrl), .result(result)
);
bind top_module top_module_sva u_top_sva(
  .clk(tb_clk), .rst_n(tb_rst_n),
  .D(D), .shift_ctrl(shift_ctrl), .a(a), .b(b), .alu_ctrl(alu_ctrl), .result(result)
);