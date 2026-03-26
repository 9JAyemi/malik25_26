module Counter(CLK, RST, Q_OUT, DATA_A, ADDA, DATA_B, ADDB, DATA_C, SETC, DATA_F, SETF);

   parameter width = 1;
   parameter init = 0;

   input CLK;
   input RST;
   input [width - 1 : 0] DATA_A;
   input ADDA;
   input [width - 1 : 0] DATA_B;
   input ADDB;
   input [width - 1 : 0] DATA_C;
   input SETC;
   input [width - 1 : 0] DATA_F;
   input SETF;

   output [width - 1 : 0] Q_OUT;

   reg [width - 1 : 0] q_state;

   assign Q_OUT = q_state;

   always @(posedge CLK) begin
      if (RST) begin
         q_state <= init;
      end else if (SETF) begin
         q_state <= DATA_F;
      end else if (SETC) begin
         q_state <= DATA_C;
      end else if (ADDA) begin
         q_state <= q_state + DATA_A;
      end else if (ADDB) begin
         q_state <= q_state + DATA_B;
      end
   end

endmodule