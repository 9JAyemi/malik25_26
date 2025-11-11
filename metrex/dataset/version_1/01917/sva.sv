// SVA checker for alu. Bind this module to the DUT and drive clk/rst_n from your env.
module alu_sva_chk (
  input logic        clk,
  input logic        rst_n,
  // DUT ports
  input logic [3:0]  ctl,
  input logic [31:0] a, b,
  input logic [31:0] out,
  input logic        zero,
  input logic        oflow
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Local recomputations
  let sum     = a + b;
  let diff    = a - b;
  let add_of  = (a[31] == b[31]) && (sum[31]  != a[31]);
  let sub_of  = (a[31] != b[31]) && (diff[31] != a[31]);
  let slt_bit = ($signed(a) < $signed(b));

  // Basic sanity
  a_no_xz:    assert property (!$isunknown({a,b,ctl})));
  out_no_xz:  assert property (!$isunknown({out,zero,oflow})));

  // Zero flag
  p_zero:     assert property (zero == (out == 32'd0));

  // Opcode functional checks
  p_add:      assert property ((ctl == 4'd2)  |-> out == sum);
  p_and:      assert property ((ctl == 4'd0)  |-> out == (a & b));
  p_nor:      assert property ((ctl == 4'd12) |-> out == ~(a | b));
  p_or:       assert property ((ctl == 4'd1)  |-> out == (a | b));
  p_slt:      assert property ((ctl == 4'd7)  |-> (out[31:1] == '0 && out[0] == slt_bit));
  p_sub:      assert property ((ctl == 4'd6)  |-> out == diff);
  p_xor:      assert property ((ctl == 4'd13) |-> out == (a ^ b));
  p_default:  assert property ((ctl inside {4'd0,4'd1,4'd2,4'd6,4'd7,4'd12,4'd13}) ||
                               (out == 32'd0));

  // Overflow flag semantic checks (only when relevant)
  p_add_of:   assert property ((ctl == 4'd2) |-> (oflow == add_of));
  p_sub_of:   assert property ((ctl == 4'd6) |-> (oflow == sub_of));

  // Optional stability (combinational determinism)
  p_stable:   assert property ($stable({ctl,a,b}) |-> $stable({out,zero,oflow}));

  // Coverage
  c_add:      cover property (ctl == 4'd2);
  c_sub:      cover property (ctl == 4'd6);
  c_and:      cover property (ctl == 4'd0);
  c_or:       cover property (ctl == 4'd1);
  c_nor:      cover property (ctl == 4'd12);
  c_xor:      cover property (ctl == 4'd13);
  c_slt:      cover property (ctl == 4'd7);
  c_default:  cover property (ctl inside {4'd3,4'd4,4'd5,4'd8,4'd9,4'd10,4'd11,4'd14,4'd15});
  c_zero1:    cover property (zero);
  c_zero0:    cover property (!zero);
  c_add_of1:  cover property ((ctl == 4'd2) && add_of);
  c_add_of0:  cover property ((ctl == 4'd2) && !add_of);
  c_sub_of1:  cover property ((ctl == 4'd6) && sub_of);
  c_sub_of0:  cover property ((ctl == 4'd6) && !sub_of);
  c_slt1:     cover property ((ctl == 4'd7) && (out[0] == 1'b1));
  c_slt0:     cover property ((ctl == 4'd7) && (out[0] == 1'b0));

endmodule

// Example bind (connect clk/rst_n from your TB):
// bind alu alu_sva_chk u_alu_sva_chk (.*);  // if your TB supplies clk,rst_n in scope
// or explicitly:
// bind alu alu_sva_chk u_alu_sva_chk (.clk(tb_clk), .rst_n(tb_rst_n), .ctl(ctl), .a(a), .b(b), .out(out), .zero(zero), .oflow(oflow));