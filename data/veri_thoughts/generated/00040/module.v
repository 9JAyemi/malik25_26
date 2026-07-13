
module shift_register (Clock, ALOAD, D, SO);
  input [8:0] D;
  input Clock, ALOAD;
  output reg SO;
  reg [8:0] tmp;
  wire n22;

  // D flip-flops to store the input data
  always@(posedge Clock)
  begin
    tmp[8] <= tmp[7];
    tmp[7] <= tmp[6];
    tmp[6] <= tmp[5];
    tmp[5] <= tmp[4];
    tmp[4] <= tmp[3];
    tmp[3] <= tmp[2];
    tmp[2] <= tmp[1];
    tmp[1] <= tmp[0];
    tmp[0] <= D[0];
  end

  // Perform the shift operation
  always@(posedge Clock)
  begin  
    SO <= (ALOAD)? D[0] : tmp[1];
    tmp[8] <= (ALOAD)? D[0] : tmp[1];
  end

  // Combinational logic to generate n22
  assign n22 = ALOAD & tmp[8];
endmodule