// SVA checker for calculator
module calculator_sva
(
  input logic [3:0] a,
  input logic [3:0] b,
  input logic [1:0] op,
  input logic [3:0] result
);

  // Sample on any input change; check outputs after ##0 (NBA update)
  event in_ev;  always @(a or b or op) -> in_ev;
  event out_ev; always @(result)       -> out_ev;
  default clocking cb @(in_ev); endclocking

  // Functional correctness
  property add_correct;
    (op == 2'b00 && !$isunknown({a,b})) |-> ##0 (result == ((a + b) & 4'hF));
  endproperty
  property sub_correct;
    (op == 2'b01 && !$isunknown({a,b})) |-> ##0 (result == ((a - b) & 4'hF));
  endproperty
  property default_zero;
    !(op inside {2'b00,2'b01}) |-> ##0 (result == 4'b0000);
  endproperty

  // Result must be known when all inputs are known
  property no_x_result_when_inputs_known;
    (!$isunknown({a,b,op})) |-> ##0 (!$isunknown(result));
  endproperty

  // Result only changes when some input changed in the same timestep
  property output_change_has_input_cause;
    @(out_ev) 1 |-> ($changed(a) || $changed(b) || $changed(op));
  endproperty

  // Assertions
  a_add:     assert property (add_correct)
              else $error("ADD wrong: a=%0h b=%0h result=%0h exp=%0h", a,b,result,(a+b)&4'hF);
  a_sub:     assert property (sub_correct)
              else $error("SUB wrong: a=%0h b=%0h result=%0h exp=%0h", a,b,result,(a-b)&4'hF);
  a_default: assert property (default_zero)
              else $error("DEFAULT wrong: op=%b result=%0h (expected 0)", op, result);
  a_known:   assert property (no_x_result_when_inputs_known)
              else $error("X/Z on result with known inputs: a=%0h b=%0h op=%b result=%0h", a,b,op,result);
  a_cause:   assert property (output_change_has_input_cause)
              else $error("Result changed without input change: a=%0h b=%0h op=%b", a,b,op);

  // Compact functional coverage
  c_op_add:      cover property (@(in_ev) op == 2'b00);
  c_op_sub:      cover property (@(in_ev) op == 2'b01);
  c_op_default:  cover property (@(in_ev) !(op inside {2'b00,2'b01}));

  // Corner-case coverage: wrap-around
  c_add_overflow:  cover property (@(in_ev) op==2'b00 && ({1'b0,a} + {1'b0,b})[4]);
  c_sub_underflow: cover property (@(in_ev) op==2'b01 && ({1'b0,a} - {1'b0,b})[4]);

endmodule

// Bind into DUT
bind calculator calculator_sva u_calculator_sva(.a(a), .b(b), .op(op), .result(result));