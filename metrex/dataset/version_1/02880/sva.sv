// SVA for calculator: concise, thorough, bind-ready

module calculator_sva (
  input  logic        clk,
  input  logic        rst,
  input  logic [1:0]  op,
  input  logic [7:0]  num1,
  input  logic [7:0]  num2,
  input  logic [7:0]  result,
  input  logic        overflow,
  input  logic        divide_by_zero
);

  default clocking cb @(posedge clk); endclocking
  default disable iff (rst);

  logic past_valid;
  always_ff @(posedge clk or posedge rst) begin
    if (rst) past_valid <= 1'b0;
    else     past_valid <= 1'b1;
  end

  // Helpers
  function automatic [7:0] add8(input [7:0] a,b); add8 = a + b; endfunction
  function automatic [7:0] sub8(input [7:0] a,b); sub8 = a - b; endfunction
  function automatic [15:0] mul16(input [7:0] a,b); mul16 = a * b; endfunction
  function automatic [7:0] div8(input [7:0] a,b); div8 = (b==0) ? '0 : (a / b); endfunction
  function automatic logic ovf_add8(input [7:0] a,b);
    logic [7:0] s; begin s = a + b; ovf_add8 = (a[7]==b[7]) && (s[7]!=a[7]); end
  endfunction
  function automatic logic ovf_sub8(input [7:0] a,b);
    logic [7:0] s; begin s = a - b; ovf_sub8 = (a[7]!=b[7]) && (s[7]!=a[7]); end
  endfunction
  function automatic logic ovf_mul8(input [7:0] a,b);
    logic [15:0] p; begin p = a * b; ovf_mul8 = |p[15:8]; end
  endfunction

  // Known outputs when active
  assert property (past_valid |-> !$isunknown({result,overflow,divide_by_zero}));

  // Reset clears by next cycle
  assert property (rst |=> result==8'h00 && overflow==1'b0 && divide_by_zero==1'b0);

  // Addition semantics
  assert property (
    past_valid && $past(op==2'b00) && $past(!rst)
    |-> result == add8($past(num1),$past(num2))
        && overflow == ovf_add8($past(num1),$past(num2))
        && divide_by_zero == 1'b0
  );

  // Subtraction semantics
  assert property (
    past_valid && $past(op==2'b01) && $past(!rst)
    |-> result == sub8($past(num1),$past(num2))
        && overflow == ovf_sub8($past(num1),$past(num2))
        && divide_by_zero == 1'b0
  );

  // Multiplication semantics
  assert property (
    past_valid && $past(op==2'b10) && $past(!rst)
    |-> (ovf_mul8($past(num1),$past(num2)) ?
            (overflow==1'b1 && result==8'h00) :
            (overflow==1'b0 && result==mul16($past(num1),$past(num2))[7:0]))
        && divide_by_zero == 1'b0
  );

  // Division-by-zero handling
  assert property (
    past_valid && $past(op==2'b11) && $past(num2)==8'h00 && $past(!rst)
    |-> divide_by_zero==1'b1 && result==8'h00 && overflow==1'b0
  );

  // Division semantics (non-zero divisor)
  assert property (
    past_valid && $past(op==2'b11) && $past(num2)!=8'h00 && $past(!rst)
    |-> result == div8($past(num1),$past(num2))
        && overflow==1'b0
        && divide_by_zero==1'b0
  );

  // Flag consistency
  assert property (divide_by_zero |-> !overflow);

  // Basic operation coverage
  cover property (past_valid && $past(op==2'b00) && $past(!rst));                  // add
  cover property (past_valid && $past(op==2'b01) && $past(!rst));                  // sub
  cover property (past_valid && $past(op==2'b10) && $past(!rst));                  // mul
  cover property (past_valid && $past(op==2'b11) && $past(!rst));                  // div
  cover property (past_valid && $past(op==2'b00) && ovf_add8($past(num1),$past(num2)));
  cover property (past_valid && $past(op==2'b01) && ovf_sub8($past(num1),$past(num2)));
  cover property (past_valid && $past(op==2'b10) && ovf_mul8($past(num1),$past(num2)));
  cover property (past_valid && $past(op==2'b11) && $past(num2)==8'h00);           // div-by-zero
  cover property ($rose(rst));

endmodule

// Bind into DUT
bind calculator calculator_sva u_calculator_sva (
  .clk(clk),
  .rst(rst),
  .op(op),
  .num1(num1),
  .num2(num2),
  .result(result),
  .overflow(overflow),
  .divide_by_zero(divide_by_zero)
);