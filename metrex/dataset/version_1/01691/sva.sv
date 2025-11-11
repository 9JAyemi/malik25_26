// SVA checker for calculator
module calculator_sva (
  input logic [7:0] op1,
  input logic [7:0] op2,
  input logic [7:0] result,
  input logic       carry,
  input logic       overflow,
  input logic       error
);

  logic [15:0] prod_ref;
  logic [7:0]  q_ref, r_ref;
  logic        overflow_ref, error_ref, carry_ref;

  always_comb begin
    // Reference model
    prod_ref      = {8'h00, op1} * {8'h00, op2};
    q_ref         = (op2 == 8'h00) ? 8'h00 : op1 / op2;
    r_ref         = (op2 == 8'h00) ? 8'h00 : op1 % op2;
    overflow_ref  = (prod_ref[15:8] != 8'h00) || ((prod_ref[7] == 1'b1) && (op1[7] != op2[7]));
    error_ref     = (op2 == 8'h00);
    carry_ref     = error_ref ? 1'b0 : r_ref[7];

    // Sanity
    assert (!$isunknown({op1, op2})) else $error("calculator: X/Z on inputs");
    if (!$isunknown({op1, op2})) begin
      assert (!$isunknown({result, carry, overflow, error})) else $error("calculator: X/Z on outputs");

      // Primary functional checks
      assert (error    == error_ref)    else $error("calculator: error mismatch exp=%0b got=%0b", error_ref, error);
      assert (result   == q_ref)        else $error("calculator: result mismatch exp=%0d got=%0d (op1=%0d op2=%0d)", q_ref, result, op1, op2);
      assert (carry    == carry_ref)    else $error("calculator: carry mismatch exp=%0b got=%0b (r_ref[7]=%0b)", carry_ref, carry, r_ref[7]);
      assert (overflow == overflow_ref) else $error("calculator: overflow mismatch exp=%0b got=%0b", overflow_ref, overflow);

      // Divide-by-zero behavior
      if (error) begin
        assert (result == 8'h00) else $error("calculator: result must be 0 when error");
        assert (carry  == 1'b0)  else $error("calculator: carry must be 0 when error");
      end else begin
        // Division identities/corner cases
        assert (q_ref*op2 + r_ref == op1) else $error("calculator: q*op2 + r != op1");
        assert (r_ref < op2)              else $error("calculator: remainder >= divisor");

        if (op2 == 8'h01) begin
          assert (result == op1) else $error("calculator: /1 quotient mismatch");
          assert (carry  == 1'b0) else $error("calculator: /1 carry must be 0");
        end
        if (op2 > op1) begin
          assert (result == 8'h00)  else $error("calculator: op2>op1 must yield quotient 0");
          assert (carry  == op1[7]) else $error("calculator: op2>op1 carry should be op1[7]");
        end
        if (op2 == op1 && op1 != 8'h00) begin
          assert (result == 8'h01 && carry == 1'b0) else $error("calculator: op1==op2!=0 => q=1,r=0,carry=0");
        end
      end

      // Coverage
      cover (error);                         // divide-by-zero
      cover (!error);                        // normal divide
      cover (!error && carry);               // remainder MSB = 1
      cover (!error && !carry);              // remainder MSB = 0
      cover (overflow);                      // overflow asserted
      cover (!overflow);                     // overflow deasserted
      cover (!error && result == 8'h00);     // quotient zero
      cover (!error && result == 8'hFF);     // quotient max
      cover (!error && op2 == 8'h01);        // divide by 1
      cover (!error && op2 > op1);           // divisor > dividend
      cover ( (prod_ref[15:8] != 8'h00) );   // overflow due to high byte
      cover ( (prod_ref[15:8] == 0) && ((prod_ref[7] == 1'b1) && (op1[7] != op2[7])) ); // overflow due to sign rule
    end
  end

endmodule

// Bind into DUT
bind calculator calculator_sva sva_inst (.*);