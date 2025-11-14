// SVA for calculator
// Bind this to the DUT: bind calculator calculator_sva i_calculator_sva(.*);

module calculator_sva(
  input clk,
  input reset,
  input [1:0] op,
  input [7:0] num1,
  input [7:0] num2,
  input [7:0] result,
  input overflow,
  input zero
);

  // Clocking and disable
  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Basic X/Z hygiene on inputs/outputs when not in reset
  assert property (!$isunknown({op, num1, num2})))
    else $error("X/Z on inputs");
  assert property (!$isunknown({result, overflow, zero})))
    else $error("X/Z on outputs");

  // Reset behavior
  assert property (@(posedge clk) reset |=> (result==8'h00 && overflow==1'b0 && zero==1'b0))
    else $error("Reset values incorrect");

  // Addition
  assert property ( (op==2'b00)
    |=> ( result   == ({1'b0,$past(num1,1,reset)} + {1'b0,$past(num2,1,reset)})[7:0]
       && overflow == ({1'b0,$past(num1,1,reset)} + {1'b0,$past(num2,1,reset)})[8]
       && zero     == (({1'b0,$past(num1,1,reset)} + {1'b0,$past(num2,1,reset)})[7:0] == 8'h00) ) )
    else $error("ADD mismatch");

  // Subtraction (unsigned underflow sets overflow)
  assert property ( (op==2'b01)
    |=> ( result   == ($past(num1,1,reset) - $past(num2,1,reset))
       && overflow == ($past(num1,1,reset) <  $past(num2,1,reset))
       && zero     == (($past(num1,1,reset) -  $past(num2,1,reset)) == 8'h00) ) )
    else $error("SUB mismatch");

  // Multiplication (truncate to 8 bits, overflow if high byte nonzero)
  assert property ( (op==2'b10)
    |=> ( result   == (($past(num1,1,reset) * $past(num2,1,reset))[7:0])
       && overflow == (|($past(num1,1,reset) * $past(num2,1,reset))[15:8])
       && zero     == ((($past(num1,1,reset) * $past(num2,1,reset))[7:0]) == 8'h00) ) )
    else $error("MUL mismatch");

  // Division (divide-by-zero special case)
  assert property ( (op==2'b11 && ($past(num2,1,reset)==8'h00))
    |=> ( result==8'hFF && overflow==1'b1 && zero==1'b0 ) )
    else $error("DIV/0 mismatch");

  assert property ( (op==2'b11 && ($past(num2,1,reset)!=8'h00))
    |=> ( result   == ($past(num1,1,reset) / $past(num2,1,reset))
       && overflow == 1'b0
       && zero     == (($past(num1,1,reset) / $past(num2,1,reset)) == 8'h00) ) )
    else $error("DIV mismatch");

  // Functional coverage
  cover property (op==2'b00);
  cover property (op==2'b01);
  cover property (op==2'b10);
  cover property (op==2'b11);

  // Corner coverage per op
  cover property ( (op==2'b00) && ({1'b0,num1}+{1'b0,num2})[8] );              // add overflow
  cover property ( (op==2'b00) && (({1'b0,num1}+{1'b0,num2})[7:0]==8'h00) );   // add zero

  cover property ( (op==2'b01) && (num1 < num2) );                              // sub underflow
  cover property ( (op==2'b01) && ((num1-num2)==8'h00) );                       // sub zero

  cover property ( (op==2'b10) && (|((num1*num2)[15:8])) );                     // mul overflow
  cover property ( (op==2'b10) && (((num1*num2)[7:0])==8'h00) );                // mul zero

  cover property ( (op==2'b11) && (num2==8'h00) );                              // div by zero
  cover property ( (op==2'b11) && (num2!=8'h00) && ((num1/num2)==8'h00) );      // div zero result

endmodule

bind calculator calculator_sva i_calculator_sva(.*);