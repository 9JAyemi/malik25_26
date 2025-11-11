module fsm(X, RESET, CLOCK, Z);
  input X, RESET, CLOCK;
  output reg Z;

  // State variables
  reg [1:0] CurrentState;
  reg [1:0] NextState;

  // State codes
  parameter State0 = 2'b00, State1 = 2'b01, State2 = 2'b10, State3 = 2'b11;

  // Output logic
  always @ (CurrentState)
    begin
    case (CurrentState)
      State0: Z <= 1;
      State3: Z <= 0;
      default: Z <= 0;
    endcase
    end

  // State registers
  always @ (posedge CLOCK or posedge RESET)
    if (RESET == 1)
      CurrentState <= State0;
    else
      CurrentState <= NextState;

  // Next state logic
  always @ (CurrentState or X)
    begin
    case (CurrentState)
      State0: if (X == 0) NextState <= State1;
              else NextState <= State0;
      State1: if (X == 0) NextState <= State1;
              else NextState <= State0;
      State3: if (X == 0) NextState <= State1;
              else NextState <= State2;
      State2: NextState <= State2;
    endcase
    end

endmodule