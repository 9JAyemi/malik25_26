// SVA for calculator and CLA_adder
// Bind these checkers in your TB, e.g.:
// bind calculator  calculator_sva  u_calculator_sva (.clk(tb_clk), .rst_n(tb_rst_n));
// bind CLA_adder   cla_adder_sva   u_cla_adder_sva  (.clk(tb_clk), .rst_n(tb_rst_n));

module calculator_sva (input logic clk, rst_n);
  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Structural/functional correctness
  assert property (num1_extended == {4'b0, num1});
  assert property (num2_extended == {4'b0, num2});

  assert property ((op_type[1] == 1'b0) |-> (result == adder_out));
  assert property ((op_type[1] == 1'b1) |-> (result == multiplier_out));

  assert property ((op_type[1] == 1'b0) |-> (multiplier_out == 8'h00));
  assert property ((op_type[1] == 1'b1) |-> (multiplier_out == (num1_extended * num2_extended)));

  // Golden adder check (will flag any CLA mismatch)
  assert property (adder_out == (num1_extended + num2_extended + op_type[0]));

  // Overflow as implemented
  assert property (overflow == ((adder_out[7] == adder_out[6]) && (adder_out[6] != op_type[0])));

  // Highest-bit network (given zero-extension, these must be zero)
  assert property (highest_bit_num1 == 4'b0000);
  assert property (highest_bit_num2 == 4'b0000);
  assert property (highest_bit      == 4'b0000);

  // No X/Z on outputs
  assert property (!$isunknown({result, overflow}));

  // Minimal functional coverage
  cover property (op_type == 2'b00);
  cover property (op_type == 2'b01);
  cover property (op_type == 2'b10);
  cover property (op_type == 2'b11);

  cover property ((op_type[1] == 1'b1) && (num1 != 4'h0) && (num2 != 4'h0) && (result != 8'h00));
  cover property ((op_type[1] == 1'b1) && (num1 == 4'hF) && (num2 == 4'hF) && (result == 8'hE1));
  cover property ((op_type == 2'b00) && (num1 == 4'hF) && (num2 == 4'hF) && (adder_out == 8'd30));
  cover property (overflow == 1'b1);
endmodule


module cla_adder_sva (input logic clk, rst_n);
  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Internal signal correctness
  assert property (P == (A ^ B));
  assert property (G == (A & B));
  assert property (C_propagate[0] == Cin);
  assert property (C_generate[0]  == G[0]);

  genvar i;
  generate
    for (i = 1; i < 8; i++) begin : g_chk
      assert property (C_propagate[i] == P[i-1]);
      assert property (C_generate[i]  == (G[i] | (P[i] & C_generate[i-1])));
    end
  endgenerate

  assert property (C == (C_propagate | C_generate));

  // Check DUT’s implemented sum wiring and also the golden arithmetic
  assert property (Sum == (P ^ {8{Cin}}));                 // as coded
  assert property ({Cout, Sum} == (A + B + Cin));          // golden add

  // No X/Z on outputs
  assert property (!$isunknown({Sum, Cout}));

  // Simple coverage
  cover property (Cin == 1'b0);
  cover property (Cin == 1'b1);
  cover property ((A == 8'h0F) && (B == 8'h10) && (Cin == 1'b0));
  cover property ((A == 8'hFF) && (B == 8'h01) && (Cin == 1'b0));
endmodule