// SVA checker for Conversor_BCD_7seg
// Bind example (provide your own clk/rst):
// bind Conversor_BCD_7seg bcd7seg_sva u_bcd7seg_sva(.clk(tb_clk), .rst_n(tb_rst_n),
//                                                   .Valor_Decimal(Valor_Decimal), .Code_7seg(Code_7seg));

module bcd7seg_sva (
  input  logic        clk,
  input  logic        rst_n,
  input  logic [3:0]  Valor_Decimal,
  input  logic [7:0]  Code_7seg
);

  function automatic logic [7:0] expected_code (input logic [3:0] v);
    case (v)
      4'h0: expected_code = 8'b00000011;
      4'h1: expected_code = 8'b10011111;
      4'h2: expected_code = 8'b00100101;
      4'h3: expected_code = 8'b00001101;
      4'h4: expected_code = 8'b10011001;
      4'h5: expected_code = 8'b01001001;
      4'h6: expected_code = 8'b01000001;
      4'h7: expected_code = 8'b00011111;
      4'h8: expected_code = 8'b00000001;
      4'h9: expected_code = 8'b00001001;
      default: expected_code = 8'b11111111;
    endcase
  endfunction

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n)

  // No X/Z on inputs/outputs
  a_no_x_in:   assert property (!$isunknown(Valor_Decimal));
  a_no_x_out:  assert property (!$isunknown(Code_7seg));

  // Functional equivalence to truth table (combinational, zero-latency)
  a_map:       assert property (Code_7seg == expected_code(Valor_Decimal));

  // Default code only for invalid inputs
  a_ff_only_on_invalid: assert property ((Code_7seg == 8'hFF) |-> (Valor_Decimal > 4'd9));

  // Output stability when input stable
  a_stable:    assert property ($stable(Valor_Decimal) |-> $stable(Code_7seg));

  // Coverage: see each input value (0-15) and corresponding driven code
  genvar i;
  generate
    for (i = 0; i < 16; i++) begin : g_cov_vals
      c_seen_val: cover property (Valor_Decimal == i[3:0] && Code_7seg == expected_code(i[3:0]));
    end
  endgenerate

  // Coverage: observe at least one invalid input usage
  c_invalid_seen: cover property (Valor_Decimal > 4'd9 && Code_7seg == 8'hFF);

  // Coverage: observe at least one instance of each valid digit
  c_digit0: cover property (Valor_Decimal==4'h0 && Code_7seg==expected_code(4'h0));
  c_digit1: cover property (Valor_Decimal==4'h1 && Code_7seg==expected_code(4'h1));
  c_digit2: cover property (Valor_Decimal==4'h2 && Code_7seg==expected_code(4'h2));
  c_digit3: cover property (Valor_Decimal==4'h3 && Code_7seg==expected_code(4'h3));
  c_digit4: cover property (Valor_Decimal==4'h4 && Code_7seg==expected_code(4'h4));
  c_digit5: cover property (Valor_Decimal==4'h5 && Code_7seg==expected_code(4'h5));
  c_digit6: cover property (Valor_Decimal==4'h6 && Code_7seg==expected_code(4'h6));
  c_digit7: cover property (Valor_Decimal==4'h7 && Code_7seg==expected_code(4'h7));
  c_digit8: cover property (Valor_Decimal==4'h8 && Code_7seg==expected_code(4'h8));
  c_digit9: cover property (Valor_Decimal==4'h9 && Code_7seg==expected_code(4'h9));

endmodule