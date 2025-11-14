// SVA for calculator (bind or instantiate with a free-running clk and active-high rst)
module calculator_sva (
  input logic              clk,
  input logic              rst,
  input logic [7:0]        input1,
  input logic [7:0]        input2,
  input logic [2:0]        opcode,
  input logic [7:0]        result
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst);

  // Helpers
  let known      = !$isunknown({opcode,input1,input2});
  let is_div     = (opcode == 3'b011);
  let div0       = known && is_div && (input2 == 8'h00);

  // Expected result (guard div0 by substituting 1; div0 is checked separately)
  let exp_val =
      (opcode==3'b000) ? (logic [7:0]'(input1 + input2)) :
      (opcode==3'b001) ? (logic [7:0]'(input1 - input2)) :
      (opcode==3'b010) ? (logic [7:0]'(input1 * input2)) :
      (opcode==3'b011) ? (logic [7:0]'(input1 / (input2==8'h00 ? 8'h01 : input2))) :
      (opcode==3'b100) ? (input1 & input2) :
      (opcode==3'b101) ? (input1 | input2) :
      (opcode==3'b110) ? (input1 ^ input2) :
                         (~input1);

  // Functional correctness (for known inputs and not div-by-zero)
  a_func:    assert property (known && !div0 |-> result == exp_val)
             else $error("calculator: functional mismatch");

  // Divide-by-zero should yield X result
  a_div0_x:  assert property (div0 |-> $isunknown(result))
             else $error("calculator: divide-by-zero should drive X");

  // Purely combinational/stable when inputs stable
  a_stable:  assert property (known && $stable({input1,input2,opcode}) |-> $stable(result))
             else $error("calculator: result changed while inputs stable");

  // Result shall be known for known inputs except div-by-zero
  a_known:   assert property (known && !div0 |-> !$isunknown(result))
             else $error("calculator: unexpected X/Z on result");

  // Opcode coverage
  c_add: cover property (known && opcode==3'b000);
  c_sub: cover property (known && opcode==3'b001);
  c_mul: cover property (known && opcode==3'b010);
  c_div: cover property (known && opcode==3'b011 && input2!=0);
  c_and: cover property (known && opcode==3'b100);
  c_or : cover property (known && opcode==3'b101);
  c_xor: cover property (known && opcode==3'b110);
  c_not: cover property (known && opcode==3'b111);

  // Corner-case coverage
  c_add_carry:      cover property (known && opcode==3'b000 && ({1'b0,input1}+{1'b0,input2})[8]);
  c_sub_borrow:     cover property (known && opcode==3'b001 && (input1 < input2));
  c_mul_overflow:   cover property (known && opcode==3'b010 && (({8'b0,input1}*{8'b0,input2})[15:8] != 0));
  c_div_remainder:  cover property (known && opcode==3'b011 && input2!=0 && (input1 % input2)!=0);
  c_div_by_zero:    cover property (known && opcode==3'b011 && input2==0);
  c_and_zero:       cover property (known && opcode==3'b100 && ((input1 & input2)==8'h00));
  c_or_full:        cover property (known && opcode==3'b101 && ((input1 | input2)==8'hFF));
  c_xor_nonzero:    cover property (known && opcode==3'b110 && ((input1 ^ input2)!=8'h00));
  c_not_patterns1:  cover property (known && opcode==3'b111 && input1==8'hAA);
  c_not_patterns2:  cover property (known && opcode==3'b111 && input1==8'h55);

endmodule

// Example bind (edit clk/rst paths to your environment):
// bind calculator calculator_sva u_calculator_sva (.* , .clk(tb_clk), .rst(tb_rst));