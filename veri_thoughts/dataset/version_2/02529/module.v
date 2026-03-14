
module add_sub_carry_out(
    output [3:0] S,
    input  [30:0] Q_reg,
    input  [6:0] Q,
    input  FSM_exp_operation_A_S,
    input  [1:0] FSM_selector_B,
    input  DI
);

  wire [31:0] A;
  wire [31:0] B;
  wire [32:0] C;
  wire carry_out;
  reg [30:0] Q_reg_temp;

  assign A = {1'b0, Q_reg};
  assign B = {1'b0, Q};

  // Perform addition or subtraction based on FSM_exp_operation_A_S
  assign C = FSM_exp_operation_A_S ? A + B : A - B;

  // Register the carry out value
  assign carry_out = C[31];

  // Store the carry out in the most significant bit of Q_reg
  always @(*)
  begin
    Q_reg_temp = Q_reg;
    Q_reg_temp[30] = carry_out;
  end

  // Select the appropriate bits of C for the output
  assign S = C[3:0];

endmodule